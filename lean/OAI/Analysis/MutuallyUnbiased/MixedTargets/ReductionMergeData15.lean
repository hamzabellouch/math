import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData15
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData16
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData14

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge480 : Integer.Sparse Master := [(Sum.inr 642, -7838560195140648960000), (Sum.inr 643, 3501219910680576000000)]

def originalMerge480 : Integer.Sparse OriginalKey := originalTerm482 ++ originalTerm483

theorem reducedMerge480Check : reducedMerge480 = Integer.Sparse.mergeBy masterLess reducedTerm482 reducedTerm483 := by decide +kernel

def reducedMerge481 : Integer.Sparse Master := [(Sum.inr 653, 892167378500321280000), (Sum.inr 654, 315973519843000320000)]

def originalMerge481 : Integer.Sparse OriginalKey := originalTerm484 ++ originalTerm485

theorem reducedMerge481Check : reducedMerge481 = Integer.Sparse.mergeBy masterLess reducedTerm484 reducedTerm485 := by decide +kernel

def reducedMerge482 : Integer.Sparse Master := [(Sum.inr 642, -7838560195140648960000), (Sum.inr 643, 3501219910680576000000), (Sum.inr 653, 892167378500321280000), (Sum.inr 654, 315973519843000320000)]

def originalMerge482 : Integer.Sparse OriginalKey := originalMerge480 ++ originalMerge481

theorem reducedMerge482Check : reducedMerge482 = Integer.Sparse.mergeBy masterLess reducedMerge480 reducedMerge481 := by decide +kernel

def reducedMerge483 : Integer.Sparse Master := [(Sum.inr 639, -3501219910680576000000), (Sum.inr 640, -5023829814312960000000), (Sum.inr 641, 2600840819146752000000), (Sum.inr 642, -7838560195140648960000), (Sum.inr 643, 3501219910680576000000), (Sum.inr 653, 892167378500321280000), (Sum.inr 654, 315973519843000320000)]

def originalMerge483 : Integer.Sparse OriginalKey := originalMerge479 ++ originalMerge482

theorem reducedMerge483Check : reducedMerge483 = Integer.Sparse.mergeBy masterLess reducedMerge479 reducedMerge482 := by decide +kernel

def reducedMerge484 : Integer.Sparse Master := [(Sum.inr 909, 8659257895151861760000), (Sum.inr 911, 7407336363717427200000)]

def originalMerge484 : Integer.Sparse OriginalKey := originalTerm486 ++ originalTerm487

theorem reducedMerge484Check : reducedMerge484 = Integer.Sparse.mergeBy masterLess reducedTerm486 reducedTerm487 := by decide +kernel

def reducedMerge485 : Integer.Sparse Master := [(Sum.inr 914, 8137792988223897600000), (Sum.inr 922, 842806262366208000000)]

def originalMerge485 : Integer.Sparse OriginalKey := originalTerm488 ++ originalTerm489

theorem reducedMerge485Check : reducedMerge485 = Integer.Sparse.mergeBy masterLess reducedTerm488 reducedTerm489 := by decide +kernel

def reducedMerge486 : Integer.Sparse Master := [(Sum.inr 909, 8659257895151861760000), (Sum.inr 911, 7407336363717427200000), (Sum.inr 914, 8137792988223897600000), (Sum.inr 922, 842806262366208000000)]

def originalMerge486 : Integer.Sparse OriginalKey := originalMerge484 ++ originalMerge485

theorem reducedMerge486Check : reducedMerge486 = Integer.Sparse.mergeBy masterLess reducedMerge484 reducedMerge485 := by decide +kernel

def reducedMerge487 : Integer.Sparse Master := [(Sum.inr 929, -941481721225543680000), (Sum.inr 930, -4522163694065418240000)]

def originalMerge487 : Integer.Sparse OriginalKey := originalTerm490 ++ originalTerm491

theorem reducedMerge487Check : reducedMerge487 = Integer.Sparse.mergeBy masterLess reducedTerm490 reducedTerm491 := by decide +kernel

def reducedMerge488 : Integer.Sparse Master := [(Sum.inr 931, 862331180804997120000), (Sum.inr 932, -2281209943794647040000)]

def originalMerge488 : Integer.Sparse OriginalKey := originalTerm492 ++ originalTerm493

theorem reducedMerge488Check : reducedMerge488 = Integer.Sparse.mergeBy masterLess reducedTerm492 reducedTerm493 := by decide +kernel

def reducedMerge489 : Integer.Sparse Master := [(Sum.inr 929, -941481721225543680000), (Sum.inr 930, -4522163694065418240000), (Sum.inr 931, 862331180804997120000), (Sum.inr 932, -2281209943794647040000)]

def originalMerge489 : Integer.Sparse OriginalKey := originalMerge487 ++ originalMerge488

theorem reducedMerge489Check : reducedMerge489 = Integer.Sparse.mergeBy masterLess reducedMerge487 reducedMerge488 := by decide +kernel

def reducedMerge490 : Integer.Sparse Master := [(Sum.inr 909, 8659257895151861760000), (Sum.inr 911, 7407336363717427200000), (Sum.inr 914, 8137792988223897600000), (Sum.inr 922, 842806262366208000000), (Sum.inr 929, -941481721225543680000), (Sum.inr 930, -4522163694065418240000), (Sum.inr 931, 862331180804997120000), (Sum.inr 932, -2281209943794647040000)]

def originalMerge490 : Integer.Sparse OriginalKey := originalMerge486 ++ originalMerge489

theorem reducedMerge490Check : reducedMerge490 = Integer.Sparse.mergeBy masterLess reducedMerge486 reducedMerge489 := by decide +kernel

def reducedMerge491 : Integer.Sparse Master := [(Sum.inr 639, -3501219910680576000000), (Sum.inr 640, -5023829814312960000000), (Sum.inr 641, 2600840819146752000000), (Sum.inr 642, -7838560195140648960000), (Sum.inr 643, 3501219910680576000000), (Sum.inr 653, 892167378500321280000), (Sum.inr 654, 315973519843000320000), (Sum.inr 909, 8659257895151861760000), (Sum.inr 911, 7407336363717427200000), (Sum.inr 914, 8137792988223897600000), (Sum.inr 922, 842806262366208000000), (Sum.inr 929, -941481721225543680000), (Sum.inr 930, -4522163694065418240000), (Sum.inr 931, 862331180804997120000), (Sum.inr 932, -2281209943794647040000)]

def originalMerge491 : Integer.Sparse OriginalKey := originalMerge483 ++ originalMerge490

theorem reducedMerge491Check : reducedMerge491 = Integer.Sparse.mergeBy masterLess reducedMerge483 reducedMerge490 := by decide +kernel

def reducedMerge492 : Integer.Sparse Master := [(Sum.inr 934, 1048155974782156800000), (Sum.inr 936, -3501622812129361920000)]

def originalMerge492 : Integer.Sparse OriginalKey := originalTerm495 ++ originalTerm496

theorem reducedMerge492Check : reducedMerge492 = Integer.Sparse.mergeBy masterLess reducedTerm495 reducedTerm496 := by decide +kernel

def reducedMerge493 : Integer.Sparse Master := [(Sum.inr 933, -842806262366208000000), (Sum.inr 934, 1048155974782156800000), (Sum.inr 936, -3501622812129361920000)]

def originalMerge493 : Integer.Sparse OriginalKey := originalTerm494 ++ originalMerge492

theorem reducedMerge493Check : reducedMerge493 = Integer.Sparse.mergeBy masterLess reducedTerm494 reducedMerge492 := by decide +kernel

def reducedMerge494 : Integer.Sparse Master := [(Sum.inr 937, -690110044530278400000), (Sum.inr 939, -5644648033344552960000)]

def originalMerge494 : Integer.Sparse OriginalKey := originalTerm497 ++ originalTerm498

theorem reducedMerge494Check : reducedMerge494 = Integer.Sparse.mergeBy masterLess reducedTerm497 reducedTerm498 := by decide +kernel

def reducedMerge495 : Integer.Sparse Master := [(Sum.inr 940, -3110224913045913600000), (Sum.inr 944, 5755499567677440000000)]

def originalMerge495 : Integer.Sparse OriginalKey := originalTerm499 ++ originalTerm500

theorem reducedMerge495Check : reducedMerge495 = Integer.Sparse.mergeBy masterLess reducedTerm499 reducedTerm500 := by decide +kernel

def reducedMerge496 : Integer.Sparse Master := [(Sum.inr 937, -690110044530278400000), (Sum.inr 939, -5644648033344552960000), (Sum.inr 940, -3110224913045913600000), (Sum.inr 944, 5755499567677440000000)]

def originalMerge496 : Integer.Sparse OriginalKey := originalMerge494 ++ originalMerge495

theorem reducedMerge496Check : reducedMerge496 = Integer.Sparse.mergeBy masterLess reducedMerge494 reducedMerge495 := by decide +kernel

def reducedMerge497 : Integer.Sparse Master := [(Sum.inr 933, -842806262366208000000), (Sum.inr 934, 1048155974782156800000), (Sum.inr 936, -3501622812129361920000), (Sum.inr 937, -690110044530278400000), (Sum.inr 939, -5644648033344552960000), (Sum.inr 940, -3110224913045913600000), (Sum.inr 944, 5755499567677440000000)]

def originalMerge497 : Integer.Sparse OriginalKey := originalMerge493 ++ originalMerge496

theorem reducedMerge497Check : reducedMerge497 = Integer.Sparse.mergeBy masterLess reducedMerge493 reducedMerge496 := by decide +kernel

def reducedMerge498 : Integer.Sparse Master := [(Sum.inr 945, 5755499567677440000000), (Sum.inr 946, 4959624732475392000000)]

def originalMerge498 : Integer.Sparse OriginalKey := originalTerm501 ++ originalTerm502

theorem reducedMerge498Check : reducedMerge498 = Integer.Sparse.mergeBy masterLess reducedTerm501 reducedTerm502 := by decide +kernel

def reducedMerge499 : Integer.Sparse Master := [(Sum.inr 949, -7458564352880148480000), (Sum.inr 950, -5755499567677440000000)]

def originalMerge499 : Integer.Sparse OriginalKey := originalTerm503 ++ originalTerm504

theorem reducedMerge499Check : reducedMerge499 = Integer.Sparse.mergeBy masterLess reducedTerm503 reducedTerm504 := by decide +kernel

def reducedMerge500 : Integer.Sparse Master := [(Sum.inr 945, 5755499567677440000000), (Sum.inr 946, 4959624732475392000000), (Sum.inr 949, -7458564352880148480000), (Sum.inr 950, -5755499567677440000000)]

def originalMerge500 : Integer.Sparse OriginalKey := originalMerge498 ++ originalMerge499

theorem reducedMerge500Check : reducedMerge500 = Integer.Sparse.mergeBy masterLess reducedMerge498 reducedMerge499 := by decide +kernel

def reducedMerge501 : Integer.Sparse Master := [(Sum.inr 951, 7458564352880148480000), (Sum.inr 952, -4959624732475392000000)]

def originalMerge501 : Integer.Sparse OriginalKey := originalTerm505 ++ originalTerm506

theorem reducedMerge501Check : reducedMerge501 = Integer.Sparse.mergeBy masterLess reducedTerm505 reducedTerm506 := by decide +kernel

def reducedMerge502 : Integer.Sparse Master := [(Sum.inr 953, -5755499567677440000000), (Sum.inr 954, -3501219910680576000000)]

def originalMerge502 : Integer.Sparse OriginalKey := originalTerm507 ++ originalTerm508

theorem reducedMerge502Check : reducedMerge502 = Integer.Sparse.mergeBy masterLess reducedTerm507 reducedTerm508 := by decide +kernel

def reducedMerge503 : Integer.Sparse Master := [(Sum.inr 951, 7458564352880148480000), (Sum.inr 952, -4959624732475392000000), (Sum.inr 953, -5755499567677440000000), (Sum.inr 954, -3501219910680576000000)]

def originalMerge503 : Integer.Sparse OriginalKey := originalMerge501 ++ originalMerge502

theorem reducedMerge503Check : reducedMerge503 = Integer.Sparse.mergeBy masterLess reducedMerge501 reducedMerge502 := by decide +kernel

def reducedMerge504 : Integer.Sparse Master := [(Sum.inr 945, 5755499567677440000000), (Sum.inr 946, 4959624732475392000000), (Sum.inr 949, -7458564352880148480000), (Sum.inr 950, -5755499567677440000000), (Sum.inr 951, 7458564352880148480000), (Sum.inr 952, -4959624732475392000000), (Sum.inr 953, -5755499567677440000000), (Sum.inr 954, -3501219910680576000000)]

def originalMerge504 : Integer.Sparse OriginalKey := originalMerge500 ++ originalMerge503

theorem reducedMerge504Check : reducedMerge504 = Integer.Sparse.mergeBy masterLess reducedMerge500 reducedMerge503 := by decide +kernel

def reducedMerge505 : Integer.Sparse Master := [(Sum.inr 933, -842806262366208000000), (Sum.inr 934, 1048155974782156800000), (Sum.inr 936, -3501622812129361920000), (Sum.inr 937, -690110044530278400000), (Sum.inr 939, -5644648033344552960000), (Sum.inr 940, -3110224913045913600000), (Sum.inr 944, 5755499567677440000000), (Sum.inr 945, 5755499567677440000000), (Sum.inr 946, 4959624732475392000000), (Sum.inr 949, -7458564352880148480000), (Sum.inr 950, -5755499567677440000000), (Sum.inr 951, 7458564352880148480000), (Sum.inr 952, -4959624732475392000000), (Sum.inr 953, -5755499567677440000000), (Sum.inr 954, -3501219910680576000000)]

def originalMerge505 : Integer.Sparse OriginalKey := originalMerge497 ++ originalMerge504

theorem reducedMerge505Check : reducedMerge505 = Integer.Sparse.mergeBy masterLess reducedMerge497 reducedMerge504 := by decide +kernel

def reducedMerge506 : Integer.Sparse Master := [(Sum.inr 639, -3501219910680576000000), (Sum.inr 640, -5023829814312960000000), (Sum.inr 641, 2600840819146752000000), (Sum.inr 642, -7838560195140648960000), (Sum.inr 643, 3501219910680576000000), (Sum.inr 653, 892167378500321280000), (Sum.inr 654, 315973519843000320000), (Sum.inr 909, 8659257895151861760000), (Sum.inr 911, 7407336363717427200000), (Sum.inr 914, 8137792988223897600000), (Sum.inr 922, 842806262366208000000), (Sum.inr 929, -941481721225543680000), (Sum.inr 930, -4522163694065418240000), (Sum.inr 931, 862331180804997120000), (Sum.inr 932, -2281209943794647040000), (Sum.inr 933, -842806262366208000000), (Sum.inr 934, 1048155974782156800000), (Sum.inr 936, -3501622812129361920000), (Sum.inr 937, -690110044530278400000), (Sum.inr 939, -5644648033344552960000), (Sum.inr 940, -3110224913045913600000), (Sum.inr 944, 5755499567677440000000), (Sum.inr 945, 5755499567677440000000), (Sum.inr 946, 4959624732475392000000), (Sum.inr 949, -7458564352880148480000), (Sum.inr 950, -5755499567677440000000), (Sum.inr 951, 7458564352880148480000), (Sum.inr 952, -4959624732475392000000), (Sum.inr 953, -5755499567677440000000), (Sum.inr 954, -3501219910680576000000)]

def originalMerge506 : Integer.Sparse OriginalKey := originalMerge491 ++ originalMerge505

theorem reducedMerge506Check : reducedMerge506 = Integer.Sparse.mergeBy masterLess reducedMerge491 reducedMerge505 := by decide +kernel

def reducedMerge507 : Integer.Sparse Master := [(Sum.inr 1027, -4206296272205905920000), (Sum.inr 1039, 84218592777338880000)]

def originalMerge507 : Integer.Sparse OriginalKey := originalTerm510 ++ originalTerm511

theorem reducedMerge507Check : reducedMerge507 = Integer.Sparse.mergeBy masterLess reducedTerm510 reducedTerm511 := by decide +kernel

def reducedMerge508 : Integer.Sparse Master := [(Sum.inr 1024, -2976678613712240640000), (Sum.inr 1027, -4206296272205905920000), (Sum.inr 1039, 84218592777338880000)]

def originalMerge508 : Integer.Sparse OriginalKey := originalTerm509 ++ originalMerge507

theorem reducedMerge508Check : reducedMerge508 = Integer.Sparse.mergeBy masterLess reducedTerm509 reducedMerge507 := by decide +kernel

def reducedMerge509 : Integer.Sparse Master := [(Sum.inr 1041, -1011243447920885760000), (Sum.inr 1044, -2007773678972436480000)]

def originalMerge509 : Integer.Sparse OriginalKey := originalTerm512 ++ originalTerm513

theorem reducedMerge509Check : reducedMerge509 = Integer.Sparse.mergeBy masterLess reducedTerm512 reducedTerm513 := by decide +kernel

def reducedMerge510 : Integer.Sparse Master := [(Sum.inr 1046, 10725266364412723200000), (Sum.inr 1047, -13781464017158799360000)]

def originalMerge510 : Integer.Sparse OriginalKey := originalTerm514 ++ originalTerm515

theorem reducedMerge510Check : reducedMerge510 = Integer.Sparse.mergeBy masterLess reducedTerm514 reducedTerm515 := by decide +kernel

def reducedMerge511 : Integer.Sparse Master := [(Sum.inr 1041, -1011243447920885760000), (Sum.inr 1044, -2007773678972436480000), (Sum.inr 1046, 10725266364412723200000), (Sum.inr 1047, -13781464017158799360000)]

def originalMerge511 : Integer.Sparse OriginalKey := originalMerge509 ++ originalMerge510

theorem reducedMerge511Check : reducedMerge511 = Integer.Sparse.mergeBy masterLess reducedMerge509 reducedMerge510 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
