import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData46
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData47
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData45

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1472 : Integer.Sparse Master := [(Sum.inl 0, -68976648065706393600), (Sum.inl 1, 459894567601373184000), (Sum.inl 2, -100888314966577152000), (Sum.inl 3, -919789135202746368000), (Sum.inl 4, -381718122047668224000), (Sum.inl 12, -613192756801830912000), (Sum.inl 13, -281555797185331200000)]

def originalMerge1472 : Integer.Sparse OriginalKey := originalTerm1476 ++ originalTerm1477

theorem reducedMerge1472Check : reducedMerge1472 = Integer.Sparse.mergeBy masterLess reducedTerm1476 reducedTerm1477 := by decide +kernel

def reducedMerge1473 : Integer.Sparse Master := [(Sum.inr 3884, 22823498120703049728000), (Sum.inr 3885, 8186717116110274560000)]

def originalMerge1473 : Integer.Sparse OriginalKey := originalTerm1478 ++ originalTerm1479

theorem reducedMerge1473Check : reducedMerge1473 = Integer.Sparse.mergeBy masterLess reducedTerm1478 reducedTerm1479 := by decide +kernel

def reducedMerge1474 : Integer.Sparse Master := [(Sum.inl 0, -68976648065706393600), (Sum.inl 1, 459894567601373184000), (Sum.inl 2, -100888314966577152000), (Sum.inl 3, -919789135202746368000), (Sum.inl 4, -381718122047668224000), (Sum.inl 12, -613192756801830912000), (Sum.inl 13, -281555797185331200000), (Sum.inr 3884, 22823498120703049728000), (Sum.inr 3885, 8186717116110274560000)]

def originalMerge1474 : Integer.Sparse OriginalKey := originalMerge1472 ++ originalMerge1473

theorem reducedMerge1474Check : reducedMerge1474 = Integer.Sparse.mergeBy masterLess reducedMerge1472 reducedMerge1473 := by decide +kernel

def reducedMerge1475 : Integer.Sparse Master := [(Sum.inr 3886, 4732620707567370240000), (Sum.inr 3899, 9660737213374464000000)]

def originalMerge1475 : Integer.Sparse OriginalKey := originalTerm1480 ++ originalTerm1481

theorem reducedMerge1475Check : reducedMerge1475 = Integer.Sparse.mergeBy masterLess reducedTerm1480 reducedTerm1481 := by decide +kernel

def reducedMerge1476 : Integer.Sparse Master := [(Sum.inr 3901, -31265001811798917120000), (Sum.inr 3902, 5315776700851814400000)]

def originalMerge1476 : Integer.Sparse OriginalKey := originalTerm1482 ++ originalTerm1483

theorem reducedMerge1476Check : reducedMerge1476 = Integer.Sparse.mergeBy masterLess reducedTerm1482 reducedTerm1483 := by decide +kernel

def reducedMerge1477 : Integer.Sparse Master := [(Sum.inr 3886, 4732620707567370240000), (Sum.inr 3899, 9660737213374464000000), (Sum.inr 3901, -31265001811798917120000), (Sum.inr 3902, 5315776700851814400000)]

def originalMerge1477 : Integer.Sparse OriginalKey := originalMerge1475 ++ originalMerge1476

theorem reducedMerge1477Check : reducedMerge1477 = Integer.Sparse.mergeBy masterLess reducedMerge1475 reducedMerge1476 := by decide +kernel

def reducedMerge1478 : Integer.Sparse Master := [(Sum.inl 0, -68976648065706393600), (Sum.inl 1, 459894567601373184000), (Sum.inl 2, -100888314966577152000), (Sum.inl 3, -919789135202746368000), (Sum.inl 4, -381718122047668224000), (Sum.inl 12, -613192756801830912000), (Sum.inl 13, -281555797185331200000), (Sum.inr 3884, 22823498120703049728000), (Sum.inr 3885, 8186717116110274560000), (Sum.inr 3886, 4732620707567370240000), (Sum.inr 3899, 9660737213374464000000), (Sum.inr 3901, -31265001811798917120000), (Sum.inr 3902, 5315776700851814400000)]

def originalMerge1478 : Integer.Sparse OriginalKey := originalMerge1474 ++ originalMerge1477

theorem reducedMerge1478Check : reducedMerge1478 = Integer.Sparse.mergeBy masterLess reducedMerge1474 reducedMerge1477 := by decide +kernel

def reducedMerge1479 : Integer.Sparse Master := [(Sum.inl 0, -68976648065706393600), (Sum.inl 1, 459894567601373184000), (Sum.inl 2, -100888314966577152000), (Sum.inl 3, -919789135202746368000), (Sum.inl 4, -381718122047668224000), (Sum.inl 12, -613192756801830912000), (Sum.inl 13, -281555797185331200000), (Sum.inr 3873, -7328462957249495040000), (Sum.inr 3874, -3964459607742283776000), (Sum.inr 3875, -11965485017379962880000), (Sum.inr 3876, -7904065631923077120000), (Sum.inr 3877, 6667737054748213248000), (Sum.inr 3880, 14474271087478702080000), (Sum.inr 3881, 312413012981121024000), (Sum.inr 3884, 22823498120703049728000), (Sum.inr 3885, 8186717116110274560000), (Sum.inr 3886, 4732620707567370240000), (Sum.inr 3899, 9660737213374464000000), (Sum.inr 3901, -31265001811798917120000), (Sum.inr 3902, 5315776700851814400000)]

def originalMerge1479 : Integer.Sparse OriginalKey := originalMerge1471 ++ originalMerge1478

theorem reducedMerge1479Check : reducedMerge1479 = Integer.Sparse.mergeBy masterLess reducedMerge1471 reducedMerge1478 := by decide +kernel

def reducedMerge1480 : Integer.Sparse Master := []

def originalMerge1480 : Integer.Sparse OriginalKey := originalTerm1485 ++ originalTerm1486

theorem reducedMerge1480Check : reducedMerge1480 = Integer.Sparse.mergeBy masterLess reducedTerm1485 reducedTerm1486 := by decide +kernel

def reducedMerge1481 : Integer.Sparse Master := [(Sum.inr 3903, -30197898181904302080000)]

def originalMerge1481 : Integer.Sparse OriginalKey := originalTerm1484 ++ originalMerge1480

theorem reducedMerge1481Check : reducedMerge1481 = Integer.Sparse.mergeBy masterLess reducedTerm1484 reducedMerge1480 := by decide +kernel

def reducedMerge1482 : Integer.Sparse Master := [(Sum.inr 3906, -6895433910022963200000), (Sum.inr 3907, 20494784666407403520000)]

def originalMerge1482 : Integer.Sparse OriginalKey := originalTerm1487 ++ originalTerm1488

theorem reducedMerge1482Check : reducedMerge1482 = Integer.Sparse.mergeBy masterLess reducedTerm1487 reducedTerm1488 := by decide +kernel

def reducedMerge1483 : Integer.Sparse Master := [(Sum.inr 3909, -6141041806181990400000)]

def originalMerge1483 : Integer.Sparse OriginalKey := originalTerm1489 ++ originalTerm1490

theorem reducedMerge1483Check : reducedMerge1483 = Integer.Sparse.mergeBy masterLess reducedTerm1489 reducedTerm1490 := by decide +kernel

def reducedMerge1484 : Integer.Sparse Master := [(Sum.inr 3906, -6895433910022963200000), (Sum.inr 3907, 20494784666407403520000), (Sum.inr 3909, -6141041806181990400000)]

def originalMerge1484 : Integer.Sparse OriginalKey := originalMerge1482 ++ originalMerge1483

theorem reducedMerge1484Check : reducedMerge1484 = Integer.Sparse.mergeBy masterLess reducedMerge1482 reducedMerge1483 := by decide +kernel

def reducedMerge1485 : Integer.Sparse Master := [(Sum.inr 3903, -30197898181904302080000), (Sum.inr 3906, -6895433910022963200000), (Sum.inr 3907, 20494784666407403520000), (Sum.inr 3909, -6141041806181990400000)]

def originalMerge1485 : Integer.Sparse OriginalKey := originalMerge1481 ++ originalMerge1484

theorem reducedMerge1485Check : reducedMerge1485 = Integer.Sparse.mergeBy masterLess reducedMerge1481 reducedMerge1484 := by decide +kernel

def reducedMerge1486 : Integer.Sparse Master := [(Sum.inr 3910, 13884969959188070400000), (Sum.inr 3913, 34895135196929064960000)]

def originalMerge1486 : Integer.Sparse OriginalKey := originalTerm1491 ++ originalTerm1492

theorem reducedMerge1486Check : reducedMerge1486 = Integer.Sparse.mergeBy masterLess reducedTerm1491 reducedTerm1492 := by decide +kernel

def reducedMerge1487 : Integer.Sparse Master := [(Sum.inr 3922, 3526248379837317120000), (Sum.inr 3945, -30372260691522355200000)]

def originalMerge1487 : Integer.Sparse OriginalKey := originalTerm1493 ++ originalTerm1494

theorem reducedMerge1487Check : reducedMerge1487 = Integer.Sparse.mergeBy masterLess reducedTerm1493 reducedTerm1494 := by decide +kernel

def reducedMerge1488 : Integer.Sparse Master := [(Sum.inr 3910, 13884969959188070400000), (Sum.inr 3913, 34895135196929064960000), (Sum.inr 3922, 3526248379837317120000), (Sum.inr 3945, -30372260691522355200000)]

def originalMerge1488 : Integer.Sparse OriginalKey := originalMerge1486 ++ originalMerge1487

theorem reducedMerge1488Check : reducedMerge1488 = Integer.Sparse.mergeBy masterLess reducedMerge1486 reducedMerge1487 := by decide +kernel

def reducedMerge1489 : Integer.Sparse Master := [(Sum.inr 3946, -5798712689427087360000), (Sum.inr 3949, -7800059930768179200000)]

def originalMerge1489 : Integer.Sparse OriginalKey := originalTerm1495 ++ originalTerm1496

theorem reducedMerge1489Check : reducedMerge1489 = Integer.Sparse.mergeBy masterLess reducedTerm1495 reducedTerm1496 := by decide +kernel

def reducedMerge1490 : Integer.Sparse Master := [(Sum.inr 3954, 11604214120782495744000)]

def originalMerge1490 : Integer.Sparse OriginalKey := originalTerm1497 ++ originalTerm1498

theorem reducedMerge1490Check : reducedMerge1490 = Integer.Sparse.mergeBy masterLess reducedTerm1497 reducedTerm1498 := by decide +kernel

def reducedMerge1491 : Integer.Sparse Master := [(Sum.inr 3946, -5798712689427087360000), (Sum.inr 3949, -7800059930768179200000), (Sum.inr 3954, 11604214120782495744000)]

def originalMerge1491 : Integer.Sparse OriginalKey := originalMerge1489 ++ originalMerge1490

theorem reducedMerge1491Check : reducedMerge1491 = Integer.Sparse.mergeBy masterLess reducedMerge1489 reducedMerge1490 := by decide +kernel

def reducedMerge1492 : Integer.Sparse Master := [(Sum.inr 3910, 13884969959188070400000), (Sum.inr 3913, 34895135196929064960000), (Sum.inr 3922, 3526248379837317120000), (Sum.inr 3945, -30372260691522355200000), (Sum.inr 3946, -5798712689427087360000), (Sum.inr 3949, -7800059930768179200000), (Sum.inr 3954, 11604214120782495744000)]

def originalMerge1492 : Integer.Sparse OriginalKey := originalMerge1488 ++ originalMerge1491

theorem reducedMerge1492Check : reducedMerge1492 = Integer.Sparse.mergeBy masterLess reducedMerge1488 reducedMerge1491 := by decide +kernel

def reducedMerge1493 : Integer.Sparse Master := [(Sum.inr 3903, -30197898181904302080000), (Sum.inr 3906, -6895433910022963200000), (Sum.inr 3907, 20494784666407403520000), (Sum.inr 3909, -6141041806181990400000), (Sum.inr 3910, 13884969959188070400000), (Sum.inr 3913, 34895135196929064960000), (Sum.inr 3922, 3526248379837317120000), (Sum.inr 3945, -30372260691522355200000), (Sum.inr 3946, -5798712689427087360000), (Sum.inr 3949, -7800059930768179200000), (Sum.inr 3954, 11604214120782495744000)]

def originalMerge1493 : Integer.Sparse OriginalKey := originalMerge1485 ++ originalMerge1492

theorem reducedMerge1493Check : reducedMerge1493 = Integer.Sparse.mergeBy masterLess reducedMerge1485 reducedMerge1492 := by decide +kernel

def reducedMerge1494 : Integer.Sparse Master := [(Sum.inl 0, -68976648065706393600), (Sum.inl 1, 459894567601373184000), (Sum.inl 2, -100888314966577152000), (Sum.inl 3, -919789135202746368000), (Sum.inl 4, -381718122047668224000), (Sum.inl 12, -613192756801830912000), (Sum.inl 13, -281555797185331200000), (Sum.inr 3873, -7328462957249495040000), (Sum.inr 3874, -3964459607742283776000), (Sum.inr 3875, -11965485017379962880000), (Sum.inr 3876, -7904065631923077120000), (Sum.inr 3877, 6667737054748213248000), (Sum.inr 3880, 14474271087478702080000), (Sum.inr 3881, 312413012981121024000), (Sum.inr 3884, 22823498120703049728000), (Sum.inr 3885, 8186717116110274560000), (Sum.inr 3886, 4732620707567370240000), (Sum.inr 3899, 9660737213374464000000), (Sum.inr 3901, -31265001811798917120000), (Sum.inr 3902, 5315776700851814400000), (Sum.inr 3903, -30197898181904302080000), (Sum.inr 3906, -6895433910022963200000), (Sum.inr 3907, 20494784666407403520000), (Sum.inr 3909, -6141041806181990400000), (Sum.inr 3910, 13884969959188070400000), (Sum.inr 3913, 34895135196929064960000), (Sum.inr 3922, 3526248379837317120000), (Sum.inr 3945, -30372260691522355200000), (Sum.inr 3946, -5798712689427087360000), (Sum.inr 3949, -7800059930768179200000), (Sum.inr 3954, 11604214120782495744000)]

def originalMerge1494 : Integer.Sparse OriginalKey := originalMerge1479 ++ originalMerge1493

theorem reducedMerge1494Check : reducedMerge1494 = Integer.Sparse.mergeBy masterLess reducedMerge1479 reducedMerge1493 := by decide +kernel

def reducedMerge1495 : Integer.Sparse Master := [(Sum.inl 0, -45979014529437696000), (Sum.inl 1, 882414070531596288000), (Sum.inl 2, -192327421407916032000), (Sum.inl 3, -2579577157701992448000), (Sum.inl 4, -656668275056640000000), (Sum.inl 12, -1163093062819774464000), (Sum.inl 13, -1047543552696582144000), (Sum.inr 3826, -8130580131269836800000), (Sum.inr 3827, -27260971487782502400000), (Sum.inr 3832, 7114320400788357120000), (Sum.inr 3833, 68789051986378752000), (Sum.inr 3834, 6338956605336649728000), (Sum.inr 3835, 1889903966198169600000), (Sum.inr 3837, -19725399924241858560000), (Sum.inr 3838, 18242460342573465600000), (Sum.inr 3839, 12880096071349764096000), (Sum.inr 3840, 31561229726387601408000), (Sum.inr 3841, -20356532239770058752000), (Sum.inr 3842, 1438088403369590784000), (Sum.inr 3843, 6828082052291297280000), (Sum.inr 3845, -34395325129220751360000), (Sum.inr 3846, -12145658229120761856000), (Sum.inr 3848, -9902480791530700800000), (Sum.inr 3849, -926150382019215360000), (Sum.inr 3850, -7979084611521085440000), (Sum.inr 3854, -911950238443732992000), (Sum.inr 3857, 4770625125647646720000), (Sum.inr 3866, 3337175163583070208000), (Sum.inr 3868, 3405889229126565888000), (Sum.inr 3869, -590135600217784320000), (Sum.inr 3870, -2103251398787137536000), (Sum.inr 3871, 11553704265979330560000), (Sum.inr 3872, -5908225161862840320000), (Sum.inr 3873, -7328462957249495040000), (Sum.inr 3874, -3964459607742283776000), (Sum.inr 3875, -11965485017379962880000), (Sum.inr 3876, -7904065631923077120000), (Sum.inr 3877, 6667737054748213248000), (Sum.inr 3880, 14474271087478702080000), (Sum.inr 3881, 312413012981121024000), (Sum.inr 3884, 22823498120703049728000), (Sum.inr 3885, 8186717116110274560000), (Sum.inr 3886, 4732620707567370240000), (Sum.inr 3899, 9660737213374464000000), (Sum.inr 3901, -31265001811798917120000), (Sum.inr 3902, 5315776700851814400000), (Sum.inr 3903, -30197898181904302080000), (Sum.inr 3906, -6895433910022963200000), (Sum.inr 3907, 20494784666407403520000), (Sum.inr 3909, -6141041806181990400000), (Sum.inr 3910, 13884969959188070400000), (Sum.inr 3913, 34895135196929064960000), (Sum.inr 3922, 3526248379837317120000), (Sum.inr 3945, -30372260691522355200000), (Sum.inr 3946, -5798712689427087360000), (Sum.inr 3949, -7800059930768179200000), (Sum.inr 3954, 11604214120782495744000)]

def originalMerge1495 : Integer.Sparse OriginalKey := originalMerge1465 ++ originalMerge1494

theorem reducedMerge1495Check : reducedMerge1495 = Integer.Sparse.mergeBy masterLess reducedMerge1465 reducedMerge1494 := by decide +kernel

def reducedMerge1496 : Integer.Sparse Master := [(Sum.inr 3957, -10194471562001448960000)]

def originalMerge1496 : Integer.Sparse OriginalKey := originalTerm1500 ++ originalTerm1501

theorem reducedMerge1496Check : reducedMerge1496 = Integer.Sparse.mergeBy masterLess reducedTerm1500 reducedTerm1501 := by decide +kernel

def reducedMerge1497 : Integer.Sparse Master := [(Sum.inr 3955, -3649006690387623936000), (Sum.inr 3957, -10194471562001448960000)]

def originalMerge1497 : Integer.Sparse OriginalKey := originalTerm1499 ++ originalMerge1496

theorem reducedMerge1497Check : reducedMerge1497 = Integer.Sparse.mergeBy masterLess reducedTerm1499 reducedMerge1496 := by decide +kernel

def reducedMerge1498 : Integer.Sparse Master := [(Sum.inr 3958, -15869111358269030400000), (Sum.inr 3959, -22837858583598858240000)]

def originalMerge1498 : Integer.Sparse OriginalKey := originalTerm1502 ++ originalTerm1503

theorem reducedMerge1498Check : reducedMerge1498 = Integer.Sparse.mergeBy masterLess reducedTerm1502 reducedTerm1503 := by decide +kernel

def reducedMerge1499 : Integer.Sparse Master := [(Sum.inr 3960, 6539548315307212800000), (Sum.inr 3961, 9259209259419893760000)]

def originalMerge1499 : Integer.Sparse OriginalKey := originalTerm1504 ++ originalTerm1505

theorem reducedMerge1499Check : reducedMerge1499 = Integer.Sparse.mergeBy masterLess reducedTerm1504 reducedTerm1505 := by decide +kernel

def reducedMerge1500 : Integer.Sparse Master := [(Sum.inr 3958, -15869111358269030400000), (Sum.inr 3959, -22837858583598858240000), (Sum.inr 3960, 6539548315307212800000), (Sum.inr 3961, 9259209259419893760000)]

def originalMerge1500 : Integer.Sparse OriginalKey := originalMerge1498 ++ originalMerge1499

theorem reducedMerge1500Check : reducedMerge1500 = Integer.Sparse.mergeBy masterLess reducedMerge1498 reducedMerge1499 := by decide +kernel

def reducedMerge1501 : Integer.Sparse Master := [(Sum.inr 3955, -3649006690387623936000), (Sum.inr 3957, -10194471562001448960000), (Sum.inr 3958, -15869111358269030400000), (Sum.inr 3959, -22837858583598858240000), (Sum.inr 3960, 6539548315307212800000), (Sum.inr 3961, 9259209259419893760000)]

def originalMerge1501 : Integer.Sparse OriginalKey := originalMerge1497 ++ originalMerge1500

theorem reducedMerge1501Check : reducedMerge1501 = Integer.Sparse.mergeBy masterLess reducedMerge1497 reducedMerge1500 := by decide +kernel

def reducedMerge1502 : Integer.Sparse Master := [(Sum.inr 3963, -12658524359512227840000)]

def originalMerge1502 : Integer.Sparse OriginalKey := originalTerm1506 ++ originalTerm1507

theorem reducedMerge1502Check : reducedMerge1502 = Integer.Sparse.mergeBy masterLess reducedTerm1506 reducedTerm1507 := by decide +kernel

def reducedMerge1503 : Integer.Sparse Master := [(Sum.inr 3964, -11253260405800304640000), (Sum.inr 3972, 8806052365250789376000)]

def originalMerge1503 : Integer.Sparse OriginalKey := originalTerm1508 ++ originalTerm1509

theorem reducedMerge1503Check : reducedMerge1503 = Integer.Sparse.mergeBy masterLess reducedTerm1508 reducedTerm1509 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
