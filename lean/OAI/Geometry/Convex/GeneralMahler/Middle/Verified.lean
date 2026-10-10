import OAI.Geometry.Convex.GeneralMahler.Middle.Tab

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma CK0_11 : By (ctStep Cn) 0 11 := by
  apply byRun (ctStep Cn) 0 11 11
  · rfl
  decide +kernel
lemma CK11_22 : By (ctStep Cn) 11 22 := by
  apply byRun (ctStep Cn) 11 11 22
  · rfl
  decide +kernel
lemma CK0_22 : By (ctStep Cn) 0 22 := byJoin CK0_11 CK11_22
lemma CK22_33 : By (ctStep Cn) 22 33 := by
  apply byRun (ctStep Cn) 22 11 33
  · rfl
  decide +kernel
lemma CK33_45 : By (ctStep Cn) 33 45 := by
  apply byRun (ctStep Cn) 33 12 45
  · rfl
  decide +kernel
lemma CK22_45 : By (ctStep Cn) 22 45 := byJoin CK22_33 CK33_45
lemma CK0_45 : By (ctStep Cn) 0 45 := byJoin CK0_22 CK22_45
lemma CK45_56 : By (ctStep Cn) 45 56 := by
  apply byRun (ctStep Cn) 45 11 56
  · rfl
  decide +kernel
lemma CK56_67 : By (ctStep Cn) 56 67 := by
  apply byRun (ctStep Cn) 56 11 67
  · rfl
  decide +kernel
lemma CK45_67 : By (ctStep Cn) 45 67 := byJoin CK45_56 CK56_67
lemma CK67_78 : By (ctStep Cn) 67 78 := by
  apply byRun (ctStep Cn) 67 11 78
  · rfl
  decide +kernel
lemma CK78_90 : By (ctStep Cn) 78 90 := by
  apply byRun (ctStep Cn) 78 12 90
  · rfl
  decide +kernel
lemma CK67_90 : By (ctStep Cn) 67 90 := byJoin CK67_78 CK78_90
lemma CK45_90 : By (ctStep Cn) 45 90 := byJoin CK45_67 CK67_90
lemma CK0_90 : By (ctStep Cn) 0 90 := byJoin CK0_45 CK45_90
lemma CK90_101 : By (ctStep Cn) 90 101 := by
  apply byRun (ctStep Cn) 90 11 101
  · rfl
  decide +kernel
lemma CK101_112 : By (ctStep Cn) 101 112 := by
  apply byRun (ctStep Cn) 101 11 112
  · rfl
  decide +kernel
lemma CK90_112 : By (ctStep Cn) 90 112 := byJoin CK90_101 CK101_112
lemma CK112_123 : By (ctStep Cn) 112 123 := by
  apply byRun (ctStep Cn) 112 11 123
  · rfl
  decide +kernel
lemma CK123_135 : By (ctStep Cn) 123 135 := by
  apply byRun (ctStep Cn) 123 12 135
  · rfl
  decide +kernel
lemma CK112_135 : By (ctStep Cn) 112 135 := byJoin CK112_123 CK123_135
lemma CK90_135 : By (ctStep Cn) 90 135 := byJoin CK90_112 CK112_135
lemma CK135_146 : By (ctStep Cn) 135 146 := by
  apply byRun (ctStep Cn) 135 11 146
  · rfl
  decide +kernel
lemma CK146_157 : By (ctStep Cn) 146 157 := by
  apply byRun (ctStep Cn) 146 11 157
  · rfl
  decide +kernel
lemma CK135_157 : By (ctStep Cn) 135 157 := byJoin CK135_146 CK146_157
lemma CK157_168 : By (ctStep Cn) 157 168 := by
  apply byRun (ctStep Cn) 157 11 168
  · rfl
  decide +kernel
lemma CK168_180 : By (ctStep Cn) 168 180 := by
  apply byRun (ctStep Cn) 168 12 180
  · rfl
  decide +kernel
lemma CK157_180 : By (ctStep Cn) 157 180 := byJoin CK157_168 CK168_180
lemma CK135_180 : By (ctStep Cn) 135 180 := byJoin CK135_157 CK157_180
lemma CK90_180 : By (ctStep Cn) 90 180 := byJoin CK90_135 CK135_180
lemma CK0_180 : By (ctStep Cn) 0 180 := byJoin CK0_90 CK90_180
lemma CK180_191 : By (ctStep Cn) 180 191 := by
  apply byRun (ctStep Cn) 180 11 191
  · rfl
  decide +kernel
lemma CK191_202 : By (ctStep Cn) 191 202 := by
  apply byRun (ctStep Cn) 191 11 202
  · rfl
  decide +kernel
lemma CK180_202 : By (ctStep Cn) 180 202 := byJoin CK180_191 CK191_202
lemma CK202_213 : By (ctStep Cn) 202 213 := by
  apply byRun (ctStep Cn) 202 11 213
  · rfl
  decide +kernel
lemma CK213_225 : By (ctStep Cn) 213 225 := by
  apply byRun (ctStep Cn) 213 12 225
  · rfl
  decide +kernel
lemma CK202_225 : By (ctStep Cn) 202 225 := byJoin CK202_213 CK213_225
lemma CK180_225 : By (ctStep Cn) 180 225 := byJoin CK180_202 CK202_225
lemma CK225_236 : By (ctStep Cn) 225 236 := by
  apply byRun (ctStep Cn) 225 11 236
  · rfl
  decide +kernel
lemma CK236_247 : By (ctStep Cn) 236 247 := by
  apply byRun (ctStep Cn) 236 11 247
  · rfl
  decide +kernel
lemma CK225_247 : By (ctStep Cn) 225 247 := byJoin CK225_236 CK236_247
lemma CK247_258 : By (ctStep Cn) 247 258 := by
  apply byRun (ctStep Cn) 247 11 258
  · rfl
  decide +kernel
lemma CK258_270 : By (ctStep Cn) 258 270 := by
  apply byRun (ctStep Cn) 258 12 270
  · rfl
  decide +kernel
lemma CK247_270 : By (ctStep Cn) 247 270 := byJoin CK247_258 CK258_270
lemma CK225_270 : By (ctStep Cn) 225 270 := byJoin CK225_247 CK247_270
lemma CK180_270 : By (ctStep Cn) 180 270 := byJoin CK180_225 CK225_270
lemma CK270_281 : By (ctStep Cn) 270 281 := by
  apply byRun (ctStep Cn) 270 11 281
  · rfl
  decide +kernel
lemma CK281_292 : By (ctStep Cn) 281 292 := by
  apply byRun (ctStep Cn) 281 11 292
  · rfl
  decide +kernel
lemma CK270_292 : By (ctStep Cn) 270 292 := byJoin CK270_281 CK281_292
lemma CK292_303 : By (ctStep Cn) 292 303 := by
  apply byRun (ctStep Cn) 292 11 303
  · rfl
  decide +kernel
lemma CK303_315 : By (ctStep Cn) 303 315 := by
  apply byRun (ctStep Cn) 303 12 315
  · rfl
  decide +kernel
lemma CK292_315 : By (ctStep Cn) 292 315 := byJoin CK292_303 CK303_315
lemma CK270_315 : By (ctStep Cn) 270 315 := byJoin CK270_292 CK292_315
lemma CK315_326 : By (ctStep Cn) 315 326 := by
  apply byRun (ctStep Cn) 315 11 326
  · rfl
  decide +kernel
lemma CK326_337 : By (ctStep Cn) 326 337 := by
  apply byRun (ctStep Cn) 326 11 337
  · rfl
  decide +kernel
lemma CK315_337 : By (ctStep Cn) 315 337 := byJoin CK315_326 CK326_337
lemma CK337_348 : By (ctStep Cn) 337 348 := by
  apply byRun (ctStep Cn) 337 11 348
  · rfl
  decide +kernel
lemma CK348_360 : By (ctStep Cn) 348 360 := by
  apply byRun (ctStep Cn) 348 12 360
  · rfl
  decide +kernel
lemma CK337_360 : By (ctStep Cn) 337 360 := byJoin CK337_348 CK348_360
lemma CK315_360 : By (ctStep Cn) 315 360 := byJoin CK315_337 CK337_360
lemma CK270_360 : By (ctStep Cn) 270 360 := byJoin CK270_315 CK315_360
lemma CK180_360 : By (ctStep Cn) 180 360 := byJoin CK180_270 CK270_360
lemma CK0_360 : By (ctStep Cn) 0 360 := byJoin CK0_180 CK180_360
lemma CK360_371 : By (ctStep Cn) 360 371 := by
  apply byRun (ctStep Cn) 360 11 371
  · rfl
  decide +kernel
lemma CK371_382 : By (ctStep Cn) 371 382 := by
  apply byRun (ctStep Cn) 371 11 382
  · rfl
  decide +kernel
lemma CK360_382 : By (ctStep Cn) 360 382 := byJoin CK360_371 CK371_382
lemma CK382_393 : By (ctStep Cn) 382 393 := by
  apply byRun (ctStep Cn) 382 11 393
  · rfl
  decide +kernel
lemma CK393_405 : By (ctStep Cn) 393 405 := by
  apply byRun (ctStep Cn) 393 12 405
  · rfl
  decide +kernel
lemma CK382_405 : By (ctStep Cn) 382 405 := byJoin CK382_393 CK393_405
lemma CK360_405 : By (ctStep Cn) 360 405 := byJoin CK360_382 CK382_405
lemma CK405_416 : By (ctStep Cn) 405 416 := by
  apply byRun (ctStep Cn) 405 11 416
  · rfl
  decide +kernel
lemma CK416_427 : By (ctStep Cn) 416 427 := by
  apply byRun (ctStep Cn) 416 11 427
  · rfl
  decide +kernel
lemma CK405_427 : By (ctStep Cn) 405 427 := byJoin CK405_416 CK416_427
lemma CK427_438 : By (ctStep Cn) 427 438 := by
  apply byRun (ctStep Cn) 427 11 438
  · rfl
  decide +kernel
lemma CK438_450 : By (ctStep Cn) 438 450 := by
  apply byRun (ctStep Cn) 438 12 450
  · rfl
  decide +kernel
lemma CK427_450 : By (ctStep Cn) 427 450 := byJoin CK427_438 CK438_450
lemma CK405_450 : By (ctStep Cn) 405 450 := byJoin CK405_427 CK427_450
lemma CK360_450 : By (ctStep Cn) 360 450 := byJoin CK360_405 CK405_450
lemma CK450_461 : By (ctStep Cn) 450 461 := by
  apply byRun (ctStep Cn) 450 11 461
  · rfl
  decide +kernel
lemma CK461_472 : By (ctStep Cn) 461 472 := by
  apply byRun (ctStep Cn) 461 11 472
  · rfl
  decide +kernel
lemma CK450_472 : By (ctStep Cn) 450 472 := byJoin CK450_461 CK461_472
lemma CK472_483 : By (ctStep Cn) 472 483 := by
  apply byRun (ctStep Cn) 472 11 483
  · rfl
  decide +kernel
lemma CK483_495 : By (ctStep Cn) 483 495 := by
  apply byRun (ctStep Cn) 483 12 495
  · rfl
  decide +kernel
lemma CK472_495 : By (ctStep Cn) 472 495 := byJoin CK472_483 CK483_495
lemma CK450_495 : By (ctStep Cn) 450 495 := byJoin CK450_472 CK472_495
lemma CK495_506 : By (ctStep Cn) 495 506 := by
  apply byRun (ctStep Cn) 495 11 506
  · rfl
  decide +kernel
lemma CK506_517 : By (ctStep Cn) 506 517 := by
  apply byRun (ctStep Cn) 506 11 517
  · rfl
  decide +kernel
lemma CK495_517 : By (ctStep Cn) 495 517 := byJoin CK495_506 CK506_517
lemma CK517_528 : By (ctStep Cn) 517 528 := by
  apply byRun (ctStep Cn) 517 11 528
  · rfl
  decide +kernel
lemma CK528_540 : By (ctStep Cn) 528 540 := by
  apply byRun (ctStep Cn) 528 12 540
  · rfl
  decide +kernel
lemma CK517_540 : By (ctStep Cn) 517 540 := byJoin CK517_528 CK528_540
lemma CK495_540 : By (ctStep Cn) 495 540 := byJoin CK495_517 CK517_540
lemma CK450_540 : By (ctStep Cn) 450 540 := byJoin CK450_495 CK495_540
lemma CK360_540 : By (ctStep Cn) 360 540 := byJoin CK360_450 CK450_540
lemma CK540_551 : By (ctStep Cn) 540 551 := by
  apply byRun (ctStep Cn) 540 11 551
  · rfl
  decide +kernel
lemma CK551_562 : By (ctStep Cn) 551 562 := by
  apply byRun (ctStep Cn) 551 11 562
  · rfl
  decide +kernel
lemma CK540_562 : By (ctStep Cn) 540 562 := byJoin CK540_551 CK551_562
lemma CK562_573 : By (ctStep Cn) 562 573 := by
  apply byRun (ctStep Cn) 562 11 573
  · rfl
  decide +kernel
lemma CK573_585 : By (ctStep Cn) 573 585 := by
  apply byRun (ctStep Cn) 573 12 585
  · rfl
  decide +kernel
lemma CK562_585 : By (ctStep Cn) 562 585 := byJoin CK562_573 CK573_585
lemma CK540_585 : By (ctStep Cn) 540 585 := byJoin CK540_562 CK562_585
lemma CK585_596 : By (ctStep Cn) 585 596 := by
  apply byRun (ctStep Cn) 585 11 596
  · rfl
  decide +kernel
lemma CK596_607 : By (ctStep Cn) 596 607 := by
  apply byRun (ctStep Cn) 596 11 607
  · rfl
  decide +kernel
lemma CK585_607 : By (ctStep Cn) 585 607 := byJoin CK585_596 CK596_607
lemma CK607_618 : By (ctStep Cn) 607 618 := by
  apply byRun (ctStep Cn) 607 11 618
  · rfl
  decide +kernel
lemma CK618_630 : By (ctStep Cn) 618 630 := by
  apply byRun (ctStep Cn) 618 12 630
  · rfl
  decide +kernel
lemma CK607_630 : By (ctStep Cn) 607 630 := byJoin CK607_618 CK618_630
lemma CK585_630 : By (ctStep Cn) 585 630 := byJoin CK585_607 CK607_630
lemma CK540_630 : By (ctStep Cn) 540 630 := byJoin CK540_585 CK585_630
lemma CK630_641 : By (ctStep Cn) 630 641 := by
  apply byRun (ctStep Cn) 630 11 641
  · rfl
  decide +kernel
lemma CK641_652 : By (ctStep Cn) 641 652 := by
  apply byRun (ctStep Cn) 641 11 652
  · rfl
  decide +kernel
lemma CK630_652 : By (ctStep Cn) 630 652 := byJoin CK630_641 CK641_652
lemma CK652_663 : By (ctStep Cn) 652 663 := by
  apply byRun (ctStep Cn) 652 11 663
  · rfl
  decide +kernel
lemma CK663_675 : By (ctStep Cn) 663 675 := by
  apply byRun (ctStep Cn) 663 12 675
  · rfl
  decide +kernel
lemma CK652_675 : By (ctStep Cn) 652 675 := byJoin CK652_663 CK663_675
lemma CK630_675 : By (ctStep Cn) 630 675 := byJoin CK630_652 CK652_675
lemma CK675_686 : By (ctStep Cn) 675 686 := by
  apply byRun (ctStep Cn) 675 11 686
  · rfl
  decide +kernel
lemma CK686_697 : By (ctStep Cn) 686 697 := by
  apply byRun (ctStep Cn) 686 11 697
  · rfl
  decide +kernel
lemma CK675_697 : By (ctStep Cn) 675 697 := byJoin CK675_686 CK686_697
lemma CK697_708 : By (ctStep Cn) 697 708 := by
  apply byRun (ctStep Cn) 697 11 708
  · rfl
  decide +kernel
lemma CK708_720 : By (ctStep Cn) 708 720 := by
  apply byRun (ctStep Cn) 708 12 720
  · rfl
  decide +kernel
lemma CK697_720 : By (ctStep Cn) 697 720 := byJoin CK697_708 CK708_720
lemma CK675_720 : By (ctStep Cn) 675 720 := byJoin CK675_697 CK697_720
lemma CK630_720 : By (ctStep Cn) 630 720 := byJoin CK630_675 CK675_720
lemma CK540_720 : By (ctStep Cn) 540 720 := byJoin CK540_630 CK630_720
lemma CK360_720 : By (ctStep Cn) 360 720 := byJoin CK360_540 CK540_720
lemma CK0_720 : By (ctStep Cn) 0 720 := byJoin CK0_360 CK360_720
lemma checkedP : Works Cn := cWorks _ (by decide +kernel) CK0_720
end GeneralMahler.SCal.Mid.Tab

end OAI
