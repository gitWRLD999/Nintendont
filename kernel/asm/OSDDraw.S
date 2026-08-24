# On-screen overlay, drawn from the PPC.
#
# Every earlier attempt had the ARM write the framebuffer, and every one of them
# black screened. That was the wrong side of the machine: ARM writes into MEM1
# while the PPC, GX and VI are all actively using it, and nothing keeps those
# coherent. Every technique that is known to work - Gecko OS in particular -
# draws from the PPC at vertical blank instead.
#
# This blob follows codehandler_stub, because that stub is already proven at this
# hook: it is branched over the terminating blr of OSSleepThread, which the game
# reaches once a frame after it has finished rendering.
#
# The framebuffer is written through the uncached mirror at 0xC0000000 rather
# than the cached one at 0x80000000, so VI sees the pixels without any cache
# maintenance. XFB is YUY2 - Y0 Cb Y1 Cr - so one 32-bit store paints two pixels.

.set VI_TFBL,   0xCC00201C   # top field base register
.set LASTFB,    0xD32C3004   # uncached scratch: framebuffer seen on the last pass
.set PIXELPAIR, 0xEB80EB80   # Y=0xEB Cb=0x80 Y=0xEB Cr=0x80, i.e. white
.set LINEBYTES, 1280         # 640 pixels at 2 bytes each
.set ROWS,      8
.set WORDS,     32           # 64 pixels at 2 pixels per store

OSDDraw:
	# disable interrupts
	mfmsr 4
	rlwinm 0,4,0,17,15
	mtmsr 0
	# save lr in the caller's slot, then make a frame
	mflr 0
	stw 0,4(1)
	stwu 1,-0x40(1)
	# save the interrupt state and every register we touch
	stw 4,0x3C(1)
	stw 3,0x38(1)
	stw 5,0x34(1)
	stw 6,0x30(1)
	stw 7,0x2C(1)
	stw 8,0x28(1)
	# save the condition and fixed-point exception registers too. The compare
	# and addic. below write both, and we are spliced into the middle of a
	# return path rather than called through the ABI, so nothing here is
	# safe to assume volatile.
	mfcr 3
	stw 3,0x24(1)
	mfxer 3
	stw 3,0x20(1)

	# r3 = VI_TFBL
	lis 3, VI_TFBL@h
	ori 3,3, VI_TFBL@l
	lwz 3,0(3)

	# r5 = address field, bits 8..31
	rlwinm 5,3,0,8,31
	# bit 28 set means the field is stored shifted right by five
	andis. 0,3,0x1000
	beq 1f
	slwi 5,5,5
1:
	# reject anything that is not plausibly a framebuffer: writing to a bad
	# address here would corrupt the running game
	andi. 0,5,31
	bne 8f
	lis 6,0x0001
	cmplw 5,6
	blt 8f
	lis 6,0x0100
	cmplw 5,6
	bge 8f

	# Only draw into an address that was also there last pass. VI_TFBL can read
	# back as something transiently wrong while the game reconfigures video, and
	# a wrong-but-plausible address means writing 8 rows straight through live
	# game data. Requiring it twice costs one frame and removes that whole class
	# of corruption.
	lis 6, LASTFB@h
	ori 6,6, LASTFB@l
	lwz 7,0(6)
	stw 5,0(6)
	cmplw 5,7
	bne 8f

	# uncached mirror, so VI sees the writes with no cache maintenance
	oris 5,5,0xC000
	# step to row 32, column 32: 32*1280 + 32*2 = 41024 bytes
	addis 5,5,1
	addi 5,5,-24512

	lis 3, PIXELPAIR@h
	ori 3,3, PIXELPAIR@l
	li 6,ROWS
2:
	li 7,WORDS
	mr 8,5
3:
	stw 3,0(8)
	addi 8,8,4
	addic. 7,7,-1
	bne 3b

	addi 5,5,LINEBYTES
	addic. 6,6,-1
	bne 2b

8:
	# restore everything and hand control back exactly as the stub does
	lwz 3,0x20(1)
	mtxer 3
	lwz 3,0x24(1)
	mtcr 3
	lwz 8,0x28(1)
	lwz 7,0x2C(1)
	lwz 6,0x30(1)
	lwz 5,0x34(1)
	lwz 3,0x38(1)
	lwz 4,0x3C(1)
	addi 1,1,0x40
	lwz 0,4(1)
	mtlr 0
	mtmsr 4
	blr
