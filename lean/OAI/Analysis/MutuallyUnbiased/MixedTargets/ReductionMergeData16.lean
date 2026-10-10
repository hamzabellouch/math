import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData16
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData17
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData15

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge512 : Integer.Sparse Master := [(Sum.inr 1024, -2976678613712240640000), (Sum.inr 1027, -4206296272205905920000), (Sum.inr 1039, 84218592777338880000), (Sum.inr 1041, -1011243447920885760000), (Sum.inr 1044, -2007773678972436480000), (Sum.inr 1046, 10725266364412723200000), (Sum.inr 1047, -13781464017158799360000)]

def originalMerge512 : Integer.Sparse OriginalKey := originalMerge508 ++ originalMerge511

theorem reducedMerge512Check : reducedMerge512 = Integer.Sparse.mergeBy masterLess reducedMerge508 reducedMerge511 := by decide +kernel

def reducedMerge513 : Integer.Sparse Master := [(Sum.inr 1049, 1567784528782295040000), (Sum.inr 1050, 927024855143546880000)]

def originalMerge513 : Integer.Sparse OriginalKey := originalTerm516 ++ originalTerm517

theorem reducedMerge513Check : reducedMerge513 = Integer.Sparse.mergeBy masterLess reducedTerm516 reducedTerm517 := by decide +kernel

def reducedMerge514 : Integer.Sparse Master := [(Sum.inr 1051, 1191593947134689280000), (Sum.inr 1058, 6300739362226176000000)]

def originalMerge514 : Integer.Sparse OriginalKey := originalTerm518 ++ originalTerm519

theorem reducedMerge514Check : reducedMerge514 = Integer.Sparse.mergeBy masterLess reducedTerm518 reducedTerm519 := by decide +kernel

def reducedMerge515 : Integer.Sparse Master := [(Sum.inr 1049, 1567784528782295040000), (Sum.inr 1050, 927024855143546880000), (Sum.inr 1051, 1191593947134689280000), (Sum.inr 1058, 6300739362226176000000)]

def originalMerge515 : Integer.Sparse OriginalKey := originalMerge513 ++ originalMerge514

theorem reducedMerge515Check : reducedMerge515 = Integer.Sparse.mergeBy masterLess reducedMerge513 reducedMerge514 := by decide +kernel

def reducedMerge516 : Integer.Sparse Master := [(Sum.inr 1061, -3750701327642787840000), (Sum.inr 1063, -6300739362226176000000)]

def originalMerge516 : Integer.Sparse OriginalKey := originalTerm520 ++ originalTerm521

theorem reducedMerge516Check : reducedMerge516 = Integer.Sparse.mergeBy masterLess reducedTerm520 reducedTerm521 := by decide +kernel

def reducedMerge517 : Integer.Sparse Master := [(Sum.inr 1064, 3750701327642787840000), (Sum.inr 1087, -8631272678361661440000)]

def originalMerge517 : Integer.Sparse OriginalKey := originalTerm522 ++ originalTerm523

theorem reducedMerge517Check : reducedMerge517 = Integer.Sparse.mergeBy masterLess reducedTerm522 reducedTerm523 := by decide +kernel

def reducedMerge518 : Integer.Sparse Master := [(Sum.inr 1061, -3750701327642787840000), (Sum.inr 1063, -6300739362226176000000), (Sum.inr 1064, 3750701327642787840000), (Sum.inr 1087, -8631272678361661440000)]

def originalMerge518 : Integer.Sparse OriginalKey := originalMerge516 ++ originalMerge517

theorem reducedMerge518Check : reducedMerge518 = Integer.Sparse.mergeBy masterLess reducedMerge516 reducedMerge517 := by decide +kernel

def reducedMerge519 : Integer.Sparse Master := [(Sum.inr 1049, 1567784528782295040000), (Sum.inr 1050, 927024855143546880000), (Sum.inr 1051, 1191593947134689280000), (Sum.inr 1058, 6300739362226176000000), (Sum.inr 1061, -3750701327642787840000), (Sum.inr 1063, -6300739362226176000000), (Sum.inr 1064, 3750701327642787840000), (Sum.inr 1087, -8631272678361661440000)]

def originalMerge519 : Integer.Sparse OriginalKey := originalMerge515 ++ originalMerge518

theorem reducedMerge519Check : reducedMerge519 = Integer.Sparse.mergeBy masterLess reducedMerge515 reducedMerge518 := by decide +kernel

def reducedMerge520 : Integer.Sparse Master := [(Sum.inr 1024, -2976678613712240640000), (Sum.inr 1027, -4206296272205905920000), (Sum.inr 1039, 84218592777338880000), (Sum.inr 1041, -1011243447920885760000), (Sum.inr 1044, -2007773678972436480000), (Sum.inr 1046, 10725266364412723200000), (Sum.inr 1047, -13781464017158799360000), (Sum.inr 1049, 1567784528782295040000), (Sum.inr 1050, 927024855143546880000), (Sum.inr 1051, 1191593947134689280000), (Sum.inr 1058, 6300739362226176000000), (Sum.inr 1061, -3750701327642787840000), (Sum.inr 1063, -6300739362226176000000), (Sum.inr 1064, 3750701327642787840000), (Sum.inr 1087, -8631272678361661440000)]

def originalMerge520 : Integer.Sparse OriginalKey := originalMerge512 ++ originalMerge519

theorem reducedMerge520Check : reducedMerge520 = Integer.Sparse.mergeBy masterLess reducedMerge512 reducedMerge519 := by decide +kernel

def reducedMerge521 : Integer.Sparse Master := [(Sum.inr 1094, -2107338916154572800000), (Sum.inr 1111, 94866766992506880000)]

def originalMerge521 : Integer.Sparse OriginalKey := originalTerm525 ++ originalTerm526

theorem reducedMerge521Check : reducedMerge521 = Integer.Sparse.mergeBy masterLess reducedTerm525 reducedTerm526 := by decide +kernel

def reducedMerge522 : Integer.Sparse Master := [(Sum.inr 1091, 7331333818189086720000), (Sum.inr 1094, -2107338916154572800000), (Sum.inr 1111, 94866766992506880000)]

def originalMerge522 : Integer.Sparse OriginalKey := originalTerm524 ++ originalMerge521

theorem reducedMerge522Check : reducedMerge522 = Integer.Sparse.mergeBy masterLess reducedTerm524 reducedMerge521 := by decide +kernel

def reducedMerge523 : Integer.Sparse Master := [(Sum.inr 1112, -26389657073487052800000), (Sum.inr 1113, -8810814575497052160000)]

def originalMerge523 : Integer.Sparse OriginalKey := originalTerm527 ++ originalTerm528

theorem reducedMerge523Check : reducedMerge523 = Integer.Sparse.mergeBy masterLess reducedTerm527 reducedTerm528 := by decide +kernel

def reducedMerge524 : Integer.Sparse Master := [(Sum.inr 1115, -1573216023167631360000), (Sum.inr 1116, -1126879414384066560000)]

def originalMerge524 : Integer.Sparse OriginalKey := originalTerm529 ++ originalTerm530

theorem reducedMerge524Check : reducedMerge524 = Integer.Sparse.mergeBy masterLess reducedTerm529 reducedTerm530 := by decide +kernel

def reducedMerge525 : Integer.Sparse Master := [(Sum.inr 1112, -26389657073487052800000), (Sum.inr 1113, -8810814575497052160000), (Sum.inr 1115, -1573216023167631360000), (Sum.inr 1116, -1126879414384066560000)]

def originalMerge525 : Integer.Sparse OriginalKey := originalMerge523 ++ originalMerge524

theorem reducedMerge525Check : reducedMerge525 = Integer.Sparse.mergeBy masterLess reducedMerge523 reducedMerge524 := by decide +kernel

def reducedMerge526 : Integer.Sparse Master := [(Sum.inr 1091, 7331333818189086720000), (Sum.inr 1094, -2107338916154572800000), (Sum.inr 1111, 94866766992506880000), (Sum.inr 1112, -26389657073487052800000), (Sum.inr 1113, -8810814575497052160000), (Sum.inr 1115, -1573216023167631360000), (Sum.inr 1116, -1126879414384066560000)]

def originalMerge526 : Integer.Sparse OriginalKey := originalMerge522 ++ originalMerge525

theorem reducedMerge526Check : reducedMerge526 = Integer.Sparse.mergeBy masterLess reducedMerge522 reducedMerge525 := by decide +kernel

def reducedMerge527 : Integer.Sparse Master := [(Sum.inr 1117, -250586732209766400000), (Sum.inr 1118, 4772950974038016000000)]

def originalMerge527 : Integer.Sparse OriginalKey := originalTerm531 ++ originalTerm532

theorem reducedMerge527Check : reducedMerge527 = Integer.Sparse.mergeBy masterLess reducedTerm531 reducedTerm532 := by decide +kernel

def reducedMerge528 : Integer.Sparse Master := [(Sum.inr 1119, -1307377367220879360000), (Sum.inr 1120, 6812136157446144000000)]

def originalMerge528 : Integer.Sparse OriginalKey := originalTerm533 ++ originalTerm534

theorem reducedMerge528Check : reducedMerge528 = Integer.Sparse.mergeBy masterLess reducedTerm533 reducedTerm534 := by decide +kernel

def reducedMerge529 : Integer.Sparse Master := [(Sum.inr 1117, -250586732209766400000), (Sum.inr 1118, 4772950974038016000000), (Sum.inr 1119, -1307377367220879360000), (Sum.inr 1120, 6812136157446144000000)]

def originalMerge529 : Integer.Sparse OriginalKey := originalMerge527 ++ originalMerge528

theorem reducedMerge529Check : reducedMerge529 = Integer.Sparse.mergeBy masterLess reducedMerge527 reducedMerge528 := by decide +kernel

def reducedMerge530 : Integer.Sparse Master := [(Sum.inr 1121, -8762782347893145600000), (Sum.inr 1125, 416003421044736000000)]

def originalMerge530 : Integer.Sparse OriginalKey := originalTerm535 ++ originalTerm536

theorem reducedMerge530Check : reducedMerge530 = Integer.Sparse.mergeBy masterLess reducedTerm535 reducedTerm536 := by decide +kernel

def reducedMerge531 : Integer.Sparse Master := [(Sum.inr 1126, 3128439995443445760000), (Sum.inr 1128, 331078441437757440000)]

def originalMerge531 : Integer.Sparse OriginalKey := originalTerm537 ++ originalTerm538

theorem reducedMerge531Check : reducedMerge531 = Integer.Sparse.mergeBy masterLess reducedTerm537 reducedTerm538 := by decide +kernel

def reducedMerge532 : Integer.Sparse Master := [(Sum.inr 1121, -8762782347893145600000), (Sum.inr 1125, 416003421044736000000), (Sum.inr 1126, 3128439995443445760000), (Sum.inr 1128, 331078441437757440000)]

def originalMerge532 : Integer.Sparse OriginalKey := originalMerge530 ++ originalMerge531

theorem reducedMerge532Check : reducedMerge532 = Integer.Sparse.mergeBy masterLess reducedMerge530 reducedMerge531 := by decide +kernel

def reducedMerge533 : Integer.Sparse Master := [(Sum.inr 1117, -250586732209766400000), (Sum.inr 1118, 4772950974038016000000), (Sum.inr 1119, -1307377367220879360000), (Sum.inr 1120, 6812136157446144000000), (Sum.inr 1121, -8762782347893145600000), (Sum.inr 1125, 416003421044736000000), (Sum.inr 1126, 3128439995443445760000), (Sum.inr 1128, 331078441437757440000)]

def originalMerge533 : Integer.Sparse OriginalKey := originalMerge529 ++ originalMerge532

theorem reducedMerge533Check : reducedMerge533 = Integer.Sparse.mergeBy masterLess reducedMerge529 reducedMerge532 := by decide +kernel

def reducedMerge534 : Integer.Sparse Master := [(Sum.inr 1091, 7331333818189086720000), (Sum.inr 1094, -2107338916154572800000), (Sum.inr 1111, 94866766992506880000), (Sum.inr 1112, -26389657073487052800000), (Sum.inr 1113, -8810814575497052160000), (Sum.inr 1115, -1573216023167631360000), (Sum.inr 1116, -1126879414384066560000), (Sum.inr 1117, -250586732209766400000), (Sum.inr 1118, 4772950974038016000000), (Sum.inr 1119, -1307377367220879360000), (Sum.inr 1120, 6812136157446144000000), (Sum.inr 1121, -8762782347893145600000), (Sum.inr 1125, 416003421044736000000), (Sum.inr 1126, 3128439995443445760000), (Sum.inr 1128, 331078441437757440000)]

def originalMerge534 : Integer.Sparse OriginalKey := originalMerge526 ++ originalMerge533

theorem reducedMerge534Check : reducedMerge534 = Integer.Sparse.mergeBy masterLess reducedMerge526 reducedMerge533 := by decide +kernel

def reducedMerge535 : Integer.Sparse Master := [(Sum.inr 1024, -2976678613712240640000), (Sum.inr 1027, -4206296272205905920000), (Sum.inr 1039, 84218592777338880000), (Sum.inr 1041, -1011243447920885760000), (Sum.inr 1044, -2007773678972436480000), (Sum.inr 1046, 10725266364412723200000), (Sum.inr 1047, -13781464017158799360000), (Sum.inr 1049, 1567784528782295040000), (Sum.inr 1050, 927024855143546880000), (Sum.inr 1051, 1191593947134689280000), (Sum.inr 1058, 6300739362226176000000), (Sum.inr 1061, -3750701327642787840000), (Sum.inr 1063, -6300739362226176000000), (Sum.inr 1064, 3750701327642787840000), (Sum.inr 1087, -8631272678361661440000), (Sum.inr 1091, 7331333818189086720000), (Sum.inr 1094, -2107338916154572800000), (Sum.inr 1111, 94866766992506880000), (Sum.inr 1112, -26389657073487052800000), (Sum.inr 1113, -8810814575497052160000), (Sum.inr 1115, -1573216023167631360000), (Sum.inr 1116, -1126879414384066560000), (Sum.inr 1117, -250586732209766400000), (Sum.inr 1118, 4772950974038016000000), (Sum.inr 1119, -1307377367220879360000), (Sum.inr 1120, 6812136157446144000000), (Sum.inr 1121, -8762782347893145600000), (Sum.inr 1125, 416003421044736000000), (Sum.inr 1126, 3128439995443445760000), (Sum.inr 1128, 331078441437757440000)]

def originalMerge535 : Integer.Sparse OriginalKey := originalMerge520 ++ originalMerge534

theorem reducedMerge535Check : reducedMerge535 = Integer.Sparse.mergeBy masterLess reducedMerge520 reducedMerge534 := by decide +kernel

def reducedMerge536 : Integer.Sparse Master := [(Sum.inr 639, -3501219910680576000000), (Sum.inr 640, -5023829814312960000000), (Sum.inr 641, 2600840819146752000000), (Sum.inr 642, -7838560195140648960000), (Sum.inr 643, 3501219910680576000000), (Sum.inr 653, 892167378500321280000), (Sum.inr 654, 315973519843000320000), (Sum.inr 909, 8659257895151861760000), (Sum.inr 911, 7407336363717427200000), (Sum.inr 914, 8137792988223897600000), (Sum.inr 922, 842806262366208000000), (Sum.inr 929, -941481721225543680000), (Sum.inr 930, -4522163694065418240000), (Sum.inr 931, 862331180804997120000), (Sum.inr 932, -2281209943794647040000), (Sum.inr 933, -842806262366208000000), (Sum.inr 934, 1048155974782156800000), (Sum.inr 936, -3501622812129361920000), (Sum.inr 937, -690110044530278400000), (Sum.inr 939, -5644648033344552960000), (Sum.inr 940, -3110224913045913600000), (Sum.inr 944, 5755499567677440000000), (Sum.inr 945, 5755499567677440000000), (Sum.inr 946, 4959624732475392000000), (Sum.inr 949, -7458564352880148480000), (Sum.inr 950, -5755499567677440000000), (Sum.inr 951, 7458564352880148480000), (Sum.inr 952, -4959624732475392000000), (Sum.inr 953, -5755499567677440000000), (Sum.inr 954, -3501219910680576000000), (Sum.inr 1024, -2976678613712240640000), (Sum.inr 1027, -4206296272205905920000), (Sum.inr 1039, 84218592777338880000), (Sum.inr 1041, -1011243447920885760000), (Sum.inr 1044, -2007773678972436480000), (Sum.inr 1046, 10725266364412723200000), (Sum.inr 1047, -13781464017158799360000), (Sum.inr 1049, 1567784528782295040000), (Sum.inr 1050, 927024855143546880000), (Sum.inr 1051, 1191593947134689280000), (Sum.inr 1058, 6300739362226176000000), (Sum.inr 1061, -3750701327642787840000), (Sum.inr 1063, -6300739362226176000000), (Sum.inr 1064, 3750701327642787840000), (Sum.inr 1087, -8631272678361661440000), (Sum.inr 1091, 7331333818189086720000), (Sum.inr 1094, -2107338916154572800000), (Sum.inr 1111, 94866766992506880000), (Sum.inr 1112, -26389657073487052800000), (Sum.inr 1113, -8810814575497052160000), (Sum.inr 1115, -1573216023167631360000), (Sum.inr 1116, -1126879414384066560000), (Sum.inr 1117, -250586732209766400000), (Sum.inr 1118, 4772950974038016000000), (Sum.inr 1119, -1307377367220879360000), (Sum.inr 1120, 6812136157446144000000), (Sum.inr 1121, -8762782347893145600000), (Sum.inr 1125, 416003421044736000000), (Sum.inr 1126, 3128439995443445760000), (Sum.inr 1128, 331078441437757440000)]

def originalMerge536 : Integer.Sparse OriginalKey := originalMerge506 ++ originalMerge535

theorem reducedMerge536Check : reducedMerge536 = Integer.Sparse.mergeBy masterLess reducedMerge506 reducedMerge535 := by decide +kernel

def reducedMerge537 : Integer.Sparse Master := [(Sum.inr 1130, -9464678117613895680000), (Sum.inr 1131, 5641023726228602880000)]

def originalMerge537 : Integer.Sparse OriginalKey := originalTerm540 ++ originalTerm541

theorem reducedMerge537Check : reducedMerge537 = Integer.Sparse.mergeBy masterLess reducedTerm540 reducedTerm541 := by decide +kernel

def reducedMerge538 : Integer.Sparse Master := [(Sum.inr 1129, 19378969510926090240000), (Sum.inr 1130, -9464678117613895680000), (Sum.inr 1131, 5641023726228602880000)]

def originalMerge538 : Integer.Sparse OriginalKey := originalTerm539 ++ originalMerge537

theorem reducedMerge538Check : reducedMerge538 = Integer.Sparse.mergeBy masterLess reducedTerm539 reducedMerge537 := by decide +kernel

def reducedMerge539 : Integer.Sparse Master := [(Sum.inr 1132, -1759585423361310720000), (Sum.inr 1133, 1307514346489774080000)]

def originalMerge539 : Integer.Sparse OriginalKey := originalTerm542 ++ originalTerm543

theorem reducedMerge539Check : reducedMerge539 = Integer.Sparse.mergeBy masterLess reducedTerm542 reducedTerm543 := by decide +kernel

def reducedMerge540 : Integer.Sparse Master := [(Sum.inr 1134, 3771399734927032320000), (Sum.inr 1135, -4459227814998835200000)]

def originalMerge540 : Integer.Sparse OriginalKey := originalTerm544 ++ originalTerm545

theorem reducedMerge540Check : reducedMerge540 = Integer.Sparse.mergeBy masterLess reducedTerm544 reducedTerm545 := by decide +kernel

def reducedMerge541 : Integer.Sparse Master := [(Sum.inr 1132, -1759585423361310720000), (Sum.inr 1133, 1307514346489774080000), (Sum.inr 1134, 3771399734927032320000), (Sum.inr 1135, -4459227814998835200000)]

def originalMerge541 : Integer.Sparse OriginalKey := originalMerge539 ++ originalMerge540

theorem reducedMerge541Check : reducedMerge541 = Integer.Sparse.mergeBy masterLess reducedMerge539 reducedMerge540 := by decide +kernel

def reducedMerge542 : Integer.Sparse Master := [(Sum.inr 1129, 19378969510926090240000), (Sum.inr 1130, -9464678117613895680000), (Sum.inr 1131, 5641023726228602880000), (Sum.inr 1132, -1759585423361310720000), (Sum.inr 1133, 1307514346489774080000), (Sum.inr 1134, 3771399734927032320000), (Sum.inr 1135, -4459227814998835200000)]

def originalMerge542 : Integer.Sparse OriginalKey := originalMerge538 ++ originalMerge541

theorem reducedMerge542Check : reducedMerge542 = Integer.Sparse.mergeBy masterLess reducedMerge538 reducedMerge541 := by decide +kernel

def reducedMerge543 : Integer.Sparse Master := [(Sum.inr 1137, 467378502645841920000), (Sum.inr 1138, -19215558570607902720000)]

def originalMerge543 : Integer.Sparse OriginalKey := originalTerm546 ++ originalTerm547

theorem reducedMerge543Check : reducedMerge543 = Integer.Sparse.mergeBy masterLess reducedTerm546 reducedTerm547 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
