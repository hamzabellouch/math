import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources40

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1120 (mixedVector B) = 0 := by
  have h4144 : mixedVector B (Sum.inr 4144) = Sparse.eval nodeValue4144 (mixedVector B) := by
    change mixedMoment B node4144 node4144Labels = _
    exact sound4144 B hB hF
  have h4146 : mixedVector B (Sum.inr 4146) = Sparse.eval nodeValue4146 (mixedVector B) := by
    change mixedMoment B node4146 node4146Labels = _
    exact sound4146 B hB hF
  have h4148 : mixedVector B (Sum.inr 4148) = Sparse.eval nodeValue4148 (mixedVector B) := by
    change mixedMoment B node4148 node4148Labels = _
    exact sound4148 B hB hF
  have h4177 : mixedVector B (Sum.inr 4177) = Sparse.eval nodeValue4177 (mixedVector B) := by
    change mixedMoment B node4177 node4177Labels = _
    exact sound4177 B hB hF
  have h4293 : mixedVector B (Sum.inr 4293) = Sparse.eval nodeValue4293 (mixedVector B) := by
    change mixedMoment B node4293 node4293Labels = _
    exact sound4293 B hB hF
  have h4315 : mixedVector B (Sum.inr 4315) = Sparse.eval nodeValue4315 (mixedVector B) := by
    change mixedMoment B node4315 node4315Labels = _
    exact sound4315 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4517 : mixedVector B (Sum.inr 4517) = Sparse.eval nodeValue4517 (mixedVector B) := by
    change mixedMoment B node4517 node4517Labels = _
    exact sound4517 B hB hF
  have h4520 : mixedVector B (Sum.inr 4520) = Sparse.eval nodeValue4520 (mixedVector B) := by
    change mixedMoment B node4520 node4520Labels = _
    exact sound4520 B hB hF
  have h4523 : mixedVector B (Sum.inr 4523) = Sparse.eval nodeValue4523 (mixedVector B) := by
    change mixedMoment B node4523 node4523Labels = _
    exact sound4523 B hB hF
  have h4526 : mixedVector B (Sum.inr 4526) = Sparse.eval nodeValue4526 (mixedVector B) := by
    change mixedMoment B node4526 node4526Labels = _
    exact sound4526 B hB hF
  have h4546 : mixedVector B (Sum.inr 4546) = Sparse.eval nodeValue4546 (mixedVector B) := by
    change mixedMoment B node4546 node4546Labels = _
    exact sound4546 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4624 : mixedVector B (Sum.inr 4624) = Sparse.eval nodeValue4624 (mixedVector B) := by
    change mixedMoment B node4624 node4624Labels = _
    exact sound4624 B hB hF
  have h4625 : mixedVector B (Sum.inr 4625) = Sparse.eval nodeValue4625 (mixedVector B) := by
    change mixedMoment B node4625 node4625Labels = _
    exact sound4625 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5109 : mixedVector B (Sum.inr 5109) = Sparse.eval nodeValue5109 (mixedVector B) := by
    change mixedMoment B node5109 node5109Labels = _
    exact sound5109 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  simpa only [sourceForm1291, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4144, h4146, h4148, h4177, h4293, h4315, h4468, h4517, h4520, h4523, h4526, h4546, h4606, h4608, h4612, h4624, h4625, h5078, h5109, h5293, h5296, reducedSource1120] using sourceEq1291 B hB

theorem rowSound1120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1120 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1120, numericCheck1120, reducedZero1120 B hB hF, mul_zero]

theorem reducedZero1121 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1121 (mixedVector B) = 0 := by
  have h572 : mixedVector B (Sum.inr 572) = Sparse.eval nodeValue572 (mixedVector B) := by
    change mixedMoment B node572 node572Labels = _
    exact sound572 B hB hF
  have h574 : mixedVector B (Sum.inr 574) = Sparse.eval nodeValue574 (mixedVector B) := by
    change mixedMoment B node574 node574Labels = _
    exact sound574 B hB hF
  have h576 : mixedVector B (Sum.inr 576) = Sparse.eval nodeValue576 (mixedVector B) := by
    change mixedMoment B node576 node576Labels = _
    exact sound576 B hB hF
  have h605 : mixedVector B (Sum.inr 605) = Sparse.eval nodeValue605 (mixedVector B) := by
    change mixedMoment B node605 node605Labels = _
    exact sound605 B hB hF
  have h871 : mixedVector B (Sum.inr 871) = Sparse.eval nodeValue871 (mixedVector B) := by
    change mixedMoment B node871 node871Labels = _
    exact sound871 B hB hF
  have h893 : mixedVector B (Sum.inr 893) = Sparse.eval nodeValue893 (mixedVector B) := by
    change mixedMoment B node893 node893Labels = _
    exact sound893 B hB hF
  have h1051 : mixedVector B (Sum.inr 1051) = Sparse.eval nodeValue1051 (mixedVector B) := by
    change mixedMoment B node1051 node1051Labels = _
    exact sound1051 B hB hF
  have h1101 : mixedVector B (Sum.inr 1101) = Sparse.eval nodeValue1101 (mixedVector B) := by
    change mixedMoment B node1101 node1101Labels = _
    exact sound1101 B hB hF
  have h1104 : mixedVector B (Sum.inr 1104) = Sparse.eval nodeValue1104 (mixedVector B) := by
    change mixedMoment B node1104 node1104Labels = _
    exact sound1104 B hB hF
  have h1107 : mixedVector B (Sum.inr 1107) = Sparse.eval nodeValue1107 (mixedVector B) := by
    change mixedMoment B node1107 node1107Labels = _
    exact sound1107 B hB hF
  have h1110 : mixedVector B (Sum.inr 1110) = Sparse.eval nodeValue1110 (mixedVector B) := by
    change mixedMoment B node1110 node1110Labels = _
    exact sound1110 B hB hF
  have h1131 : mixedVector B (Sum.inr 1131) = Sparse.eval nodeValue1131 (mixedVector B) := by
    change mixedMoment B node1131 node1131Labels = _
    exact sound1131 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h1301 : mixedVector B (Sum.inr 1301) = Sparse.eval nodeValue1301 (mixedVector B) := by
    change mixedMoment B node1301 node1301Labels = _
    exact sound1301 B hB hF
  have h1304 : mixedVector B (Sum.inr 1304) = Sparse.eval nodeValue1304 (mixedVector B) := by
    change mixedMoment B node1304 node1304Labels = _
    exact sound1304 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h2519 : mixedVector B (Sum.inr 2519) = Sparse.eval nodeValue2519 (mixedVector B) := by
    change mixedMoment B node2519 node2519Labels = _
    exact sound2519 B hB hF
  have h2770 : mixedVector B (Sum.inr 2770) = Sparse.eval nodeValue2770 (mixedVector B) := by
    change mixedMoment B node2770 node2770Labels = _
    exact sound2770 B hB hF
  have h3102 : mixedVector B (Sum.inr 3102) = Sparse.eval nodeValue3102 (mixedVector B) := by
    change mixedMoment B node3102 node3102Labels = _
    exact sound3102 B hB hF
  simpa only [sourceForm1292, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h572, h574, h576, h605, h871, h893, h1051, h1101, h1104, h1107, h1110, h1131, h1240, h1242, h1246, h1301, h1304, h2485, h2519, h2770, h3102, reducedSource1121] using sourceEq1292 B hB

theorem rowSound1121 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1121 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1121, numericCheck1121, reducedZero1121 B hB hF, mul_zero]

theorem reducedZero1122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1122 (mixedVector B) = 0 := by
  have h1617 : mixedVector B (Sum.inr 1617) = Sparse.eval nodeValue1617 (mixedVector B) := by
    change mixedMoment B node1617 node1617Labels = _
    exact sound1617 B hB hF
  have h1625 : mixedVector B (Sum.inr 1625) = Sparse.eval nodeValue1625 (mixedVector B) := by
    change mixedMoment B node1625 node1625Labels = _
    exact sound1625 B hB hF
  have h1630 : mixedVector B (Sum.inr 1630) = Sparse.eval nodeValue1630 (mixedVector B) := by
    change mixedMoment B node1630 node1630Labels = _
    exact sound1630 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1295, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1617, h1625, h1630, h1754, h3300, h4070, reducedSource1122] using sourceEq1295 B hB

theorem rowSound1122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1122 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1122, numericCheck1122, reducedZero1122 B hB hF, mul_zero]

theorem reducedZero1123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1123 (mixedVector B) = 0 := by
  have h4157 : mixedVector B (Sum.inr 4157) = Sparse.eval nodeValue4157 (mixedVector B) := by
    change mixedMoment B node4157 node4157Labels = _
    exact sound4157 B hB hF
  have h4159 : mixedVector B (Sum.inr 4159) = Sparse.eval nodeValue4159 (mixedVector B) := by
    change mixedMoment B node4159 node4159Labels = _
    exact sound4159 B hB hF
  have h4162 : mixedVector B (Sum.inr 4162) = Sparse.eval nodeValue4162 (mixedVector B) := by
    change mixedMoment B node4162 node4162Labels = _
    exact sound4162 B hB hF
  have h4184 : mixedVector B (Sum.inr 4184) = Sparse.eval nodeValue4184 (mixedVector B) := by
    change mixedMoment B node4184 node4184Labels = _
    exact sound4184 B hB hF
  have h4330 : mixedVector B (Sum.inr 4330) = Sparse.eval nodeValue4330 (mixedVector B) := by
    change mixedMoment B node4330 node4330Labels = _
    exact sound4330 B hB hF
  have h4356 : mixedVector B (Sum.inr 4356) = Sparse.eval nodeValue4356 (mixedVector B) := by
    change mixedMoment B node4356 node4356Labels = _
    exact sound4356 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4532 : mixedVector B (Sum.inr 4532) = Sparse.eval nodeValue4532 (mixedVector B) := by
    change mixedMoment B node4532 node4532Labels = _
    exact sound4532 B hB hF
  have h4536 : mixedVector B (Sum.inr 4536) = Sparse.eval nodeValue4536 (mixedVector B) := by
    change mixedMoment B node4536 node4536Labels = _
    exact sound4536 B hB hF
  have h4543 : mixedVector B (Sum.inr 4543) = Sparse.eval nodeValue4543 (mixedVector B) := by
    change mixedMoment B node4543 node4543Labels = _
    exact sound4543 B hB hF
  have h4552 : mixedVector B (Sum.inr 4552) = Sparse.eval nodeValue4552 (mixedVector B) := by
    change mixedMoment B node4552 node4552Labels = _
    exact sound4552 B hB hF
  have h4557 : mixedVector B (Sum.inr 4557) = Sparse.eval nodeValue4557 (mixedVector B) := by
    change mixedMoment B node4557 node4557Labels = _
    exact sound4557 B hB hF
  have h4600 : mixedVector B (Sum.inr 4600) = Sparse.eval nodeValue4600 (mixedVector B) := by
    change mixedMoment B node4600 node4600Labels = _
    exact sound4600 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4611 : mixedVector B (Sum.inr 4611) = Sparse.eval nodeValue4611 (mixedVector B) := by
    change mixedMoment B node4611 node4611Labels = _
    exact sound4611 B hB hF
  have h4617 : mixedVector B (Sum.inr 4617) = Sparse.eval nodeValue4617 (mixedVector B) := by
    change mixedMoment B node4617 node4617Labels = _
    exact sound4617 B hB hF
  have h4621 : mixedVector B (Sum.inr 4621) = Sparse.eval nodeValue4621 (mixedVector B) := by
    change mixedMoment B node4621 node4621Labels = _
    exact sound4621 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h5272 : mixedVector B (Sum.inr 5272) = Sparse.eval nodeValue5272 (mixedVector B) := by
    change mixedMoment B node5272 node5272Labels = _
    exact sound5272 B hB hF
  simpa only [sourceForm1296, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4157, h4159, h4162, h4184, h4330, h4356, h4468, h4532, h4536, h4543, h4552, h4557, h4600, h4605, h4611, h4617, h4621, h4804, h4841, h4897, h5272, reducedSource1123] using sourceEq1296 B hB

theorem rowSound1123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1123 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1123, numericCheck1123, reducedZero1123 B hB hF, mul_zero]

theorem reducedZero1124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1124 (mixedVector B) = 0 := by
  have h585 : mixedVector B (Sum.inr 585) = Sparse.eval nodeValue585 (mixedVector B) := by
    change mixedMoment B node585 node585Labels = _
    exact sound585 B hB hF
  have h587 : mixedVector B (Sum.inr 587) = Sparse.eval nodeValue587 (mixedVector B) := by
    change mixedMoment B node587 node587Labels = _
    exact sound587 B hB hF
  have h590 : mixedVector B (Sum.inr 590) = Sparse.eval nodeValue590 (mixedVector B) := by
    change mixedMoment B node590 node590Labels = _
    exact sound590 B hB hF
  have h612 : mixedVector B (Sum.inr 612) = Sparse.eval nodeValue612 (mixedVector B) := by
    change mixedMoment B node612 node612Labels = _
    exact sound612 B hB hF
  have h1116 : mixedVector B (Sum.inr 1116) = Sparse.eval nodeValue1116 (mixedVector B) := by
    change mixedMoment B node1116 node1116Labels = _
    exact sound1116 B hB hF
  have h1118 : mixedVector B (Sum.inr 1118) = Sparse.eval nodeValue1118 (mixedVector B) := by
    change mixedMoment B node1118 node1118Labels = _
    exact sound1118 B hB hF
  have h1121 : mixedVector B (Sum.inr 1121) = Sparse.eval nodeValue1121 (mixedVector B) := by
    change mixedMoment B node1121 node1121Labels = _
    exact sound1121 B hB hF
  have h1137 : mixedVector B (Sum.inr 1137) = Sparse.eval nodeValue1137 (mixedVector B) := by
    change mixedMoment B node1137 node1137Labels = _
    exact sound1137 B hB hF
  have h1170 : mixedVector B (Sum.inr 1170) = Sparse.eval nodeValue1170 (mixedVector B) := by
    change mixedMoment B node1170 node1170Labels = _
    exact sound1170 B hB hF
  have h1173 : mixedVector B (Sum.inr 1173) = Sparse.eval nodeValue1173 (mixedVector B) := by
    change mixedMoment B node1173 node1173Labels = _
    exact sound1173 B hB hF
  have h1177 : mixedVector B (Sum.inr 1177) = Sparse.eval nodeValue1177 (mixedVector B) := by
    change mixedMoment B node1177 node1177Labels = _
    exact sound1177 B hB hF
  have h1270 : mixedVector B (Sum.inr 1270) = Sparse.eval nodeValue1270 (mixedVector B) := by
    change mixedMoment B node1270 node1270Labels = _
    exact sound1270 B hB hF
  have h1271 : mixedVector B (Sum.inr 1271) = Sparse.eval nodeValue1271 (mixedVector B) := by
    change mixedMoment B node1271 node1271Labels = _
    exact sound1271 B hB hF
  have h1273 : mixedVector B (Sum.inr 1273) = Sparse.eval nodeValue1273 (mixedVector B) := by
    change mixedMoment B node1273 node1273Labels = _
    exact sound1273 B hB hF
  have h1275 : mixedVector B (Sum.inr 1275) = Sparse.eval nodeValue1275 (mixedVector B) := by
    change mixedMoment B node1275 node1275Labels = _
    exact sound1275 B hB hF
  have h1306 : mixedVector B (Sum.inr 1306) = Sparse.eval nodeValue1306 (mixedVector B) := by
    change mixedMoment B node1306 node1306Labels = _
    exact sound1306 B hB hF
  have h1308 : mixedVector B (Sum.inr 1308) = Sparse.eval nodeValue1308 (mixedVector B) := by
    change mixedMoment B node1308 node1308Labels = _
    exact sound1308 B hB hF
  have h2941 : mixedVector B (Sum.inr 2941) = Sparse.eval nodeValue2941 (mixedVector B) := by
    change mixedMoment B node2941 node2941Labels = _
    exact sound2941 B hB hF
  have h3004 : mixedVector B (Sum.inr 3004) = Sparse.eval nodeValue3004 (mixedVector B) := by
    change mixedMoment B node3004 node3004Labels = _
    exact sound3004 B hB hF
  have h3113 : mixedVector B (Sum.inr 3113) = Sparse.eval nodeValue3113 (mixedVector B) := by
    change mixedMoment B node3113 node3113Labels = _
    exact sound3113 B hB hF
  have h3114 : mixedVector B (Sum.inr 3114) = Sparse.eval nodeValue3114 (mixedVector B) := by
    change mixedMoment B node3114 node3114Labels = _
    exact sound3114 B hB hF
  simpa only [sourceForm1297, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h585, h587, h590, h612, h1116, h1118, h1121, h1137, h1170, h1173, h1177, h1270, h1271, h1273, h1275, h1306, h1308, h2941, h3004, h3113, h3114, reducedSource1124] using sourceEq1297 B hB

theorem rowSound1124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1124 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1124, numericCheck1124, reducedZero1124 B hB hF, mul_zero]

theorem reducedZero1125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1125 (mixedVector B) = 0 := by
  have h1528 : mixedVector B (Sum.inr 1528) = Sparse.eval nodeValue1528 (mixedVector B) := by
    change mixedMoment B node1528 node1528Labels = _
    exact sound1528 B hB hF
  have h1529 : mixedVector B (Sum.inr 1529) = Sparse.eval nodeValue1529 (mixedVector B) := by
    change mixedMoment B node1529 node1529Labels = _
    exact sound1529 B hB hF
  have h1530 : mixedVector B (Sum.inr 1530) = Sparse.eval nodeValue1530 (mixedVector B) := by
    change mixedMoment B node1530 node1530Labels = _
    exact sound1530 B hB hF
  have h1532 : mixedVector B (Sum.inr 1532) = Sparse.eval nodeValue1532 (mixedVector B) := by
    change mixedMoment B node1532 node1532Labels = _
    exact sound1532 B hB hF
  have h1672 : mixedVector B (Sum.inr 1672) = Sparse.eval nodeValue1672 (mixedVector B) := by
    change mixedMoment B node1672 node1672Labels = _
    exact sound1672 B hB hF
  have h1692 : mixedVector B (Sum.inr 1692) = Sparse.eval nodeValue1692 (mixedVector B) := by
    change mixedMoment B node1692 node1692Labels = _
    exact sound1692 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h2149 : mixedVector B (Sum.inr 2149) = Sparse.eval nodeValue2149 (mixedVector B) := by
    change mixedMoment B node2149 node2149Labels = _
    exact sound2149 B hB hF
  have h2167 : mixedVector B (Sum.inr 2167) = Sparse.eval nodeValue2167 (mixedVector B) := by
    change mixedMoment B node2167 node2167Labels = _
    exact sound2167 B hB hF
  have h2172 : mixedVector B (Sum.inr 2172) = Sparse.eval nodeValue2172 (mixedVector B) := by
    change mixedMoment B node2172 node2172Labels = _
    exact sound2172 B hB hF
  have h2184 : mixedVector B (Sum.inr 2184) = Sparse.eval nodeValue2184 (mixedVector B) := by
    change mixedMoment B node2184 node2184Labels = _
    exact sound2184 B hB hF
  have h2200 : mixedVector B (Sum.inr 2200) = Sparse.eval nodeValue2200 (mixedVector B) := by
    change mixedMoment B node2200 node2200Labels = _
    exact sound2200 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  simpa only [sourceForm1298, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1528, h1529, h1530, h1532, h1672, h1692, h1752, h2149, h2167, h2172, h2184, h2200, h2203, h2226, h2228, h2289, h2292, h2683, h2702, h2737, h2740, reducedSource1125] using sourceEq1298 B hB

theorem rowSound1125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1125 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1125, numericCheck1125, reducedZero1125 B hB hF, mul_zero]

theorem reducedZero1126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1126 (mixedVector B) = 0 := by
  have h624 : mixedVector B (Sum.inr 624) = Sparse.eval nodeValue624 (mixedVector B) := by
    change mixedMoment B node624 node624Labels = _
    exact sound624 B hB hF
  have h628 : mixedVector B (Sum.inr 628) = Sparse.eval nodeValue628 (mixedVector B) := by
    change mixedMoment B node628 node628Labels = _
    exact sound628 B hB hF
  have h634 : mixedVector B (Sum.inr 634) = Sparse.eval nodeValue634 (mixedVector B) := by
    change mixedMoment B node634 node634Labels = _
    exact sound634 B hB hF
  have h639 : mixedVector B (Sum.inr 639) = Sparse.eval nodeValue639 (mixedVector B) := by
    change mixedMoment B node639 node639Labels = _
    exact sound639 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1299, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h624, h628, h634, h639, h1239, h4084, reducedSource1126] using sourceEq1299 B hB

theorem rowSound1126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1126 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1126, numericCheck1126, reducedZero1126 B hB hF, mul_zero]

theorem reducedZero1127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1127 (mixedVector B) = 0 := by
  have h624 : mixedVector B (Sum.inr 624) = Sparse.eval nodeValue624 (mixedVector B) := by
    change mixedMoment B node624 node624Labels = _
    exact sound624 B hB hF
  have h1128 : mixedVector B (Sum.inr 1128) = Sparse.eval nodeValue1128 (mixedVector B) := by
    change mixedMoment B node1128 node1128Labels = _
    exact sound1128 B hB hF
  have h1147 : mixedVector B (Sum.inr 1147) = Sparse.eval nodeValue1147 (mixedVector B) := by
    change mixedMoment B node1147 node1147Labels = _
    exact sound1147 B hB hF
  have h1234 : mixedVector B (Sum.inr 1234) = Sparse.eval nodeValue1234 (mixedVector B) := by
    change mixedMoment B node1234 node1234Labels = _
    exact sound1234 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1300, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h624, h1128, h1147, h1234, h1239, h4084, reducedSource1127] using sourceEq1300 B hB

theorem rowSound1127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1127 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1127, numericCheck1127, reducedZero1127 B hB hF, mul_zero]

theorem reducedZero1128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1128 (mixedVector B) = 0 := by
  have h908 : mixedVector B (Sum.inr 908) = Sparse.eval nodeValue908 (mixedVector B) := by
    change mixedMoment B node908 node908Labels = _
    exact sound908 B hB hF
  have h1147 : mixedVector B (Sum.inr 1147) = Sparse.eval nodeValue1147 (mixedVector B) := by
    change mixedMoment B node1147 node1147Labels = _
    exact sound1147 B hB hF
  have h1153 : mixedVector B (Sum.inr 1153) = Sparse.eval nodeValue1153 (mixedVector B) := by
    change mixedMoment B node1153 node1153Labels = _
    exact sound1153 B hB hF
  have h1157 : mixedVector B (Sum.inr 1157) = Sparse.eval nodeValue1157 (mixedVector B) := by
    change mixedMoment B node1157 node1157Labels = _
    exact sound1157 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1301, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h908, h1147, h1153, h1157, h1239, h2022, h4084, reducedSource1128] using sourceEq1301 B hB

theorem rowSound1128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1128 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1128, numericCheck1128, reducedZero1128 B hB hF, mul_zero]

theorem reducedZero1129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1129 (mixedVector B) = 0 := by
  have h934 : mixedVector B (Sum.inr 934) = Sparse.eval nodeValue934 (mixedVector B) := by
    change mixedMoment B node934 node934Labels = _
    exact sound934 B hB hF
  have h1128 : mixedVector B (Sum.inr 1128) = Sparse.eval nodeValue1128 (mixedVector B) := by
    change mixedMoment B node1128 node1128Labels = _
    exact sound1128 B hB hF
  have h1143 : mixedVector B (Sum.inr 1143) = Sparse.eval nodeValue1143 (mixedVector B) := by
    change mixedMoment B node1143 node1143Labels = _
    exact sound1143 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h2060 : mixedVector B (Sum.inr 2060) = Sparse.eval nodeValue2060 (mixedVector B) := by
    change mixedMoment B node2060 node2060Labels = _
    exact sound2060 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1302, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h934, h1128, h1143, h1239, h2060, h4084, reducedSource1129] using sourceEq1302 B hB

theorem rowSound1129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1129 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1129, numericCheck1129, reducedZero1129 B hB hF, mul_zero]

theorem reducedZero1130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1130 (mixedVector B) = 0 := by
  have h4140 : mixedVector B (Sum.inr 4140) = Sparse.eval nodeValue4140 (mixedVector B) := by
    change mixedMoment B node4140 node4140Labels = _
    exact sound4140 B hB hF
  have h4142 : mixedVector B (Sum.inr 4142) = Sparse.eval nodeValue4142 (mixedVector B) := by
    change mixedMoment B node4142 node4142Labels = _
    exact sound4142 B hB hF
  have h4147 : mixedVector B (Sum.inr 4147) = Sparse.eval nodeValue4147 (mixedVector B) := by
    change mixedMoment B node4147 node4147Labels = _
    exact sound4147 B hB hF
  have h4174 : mixedVector B (Sum.inr 4174) = Sparse.eval nodeValue4174 (mixedVector B) := by
    change mixedMoment B node4174 node4174Labels = _
    exact sound4174 B hB hF
  have h4202 : mixedVector B (Sum.inr 4202) = Sparse.eval nodeValue4202 (mixedVector B) := by
    change mixedMoment B node4202 node4202Labels = _
    exact sound4202 B hB hF
  have h4225 : mixedVector B (Sum.inr 4225) = Sparse.eval nodeValue4225 (mixedVector B) := by
    change mixedMoment B node4225 node4225Labels = _
    exact sound4225 B hB hF
  have h4257 : mixedVector B (Sum.inr 4257) = Sparse.eval nodeValue4257 (mixedVector B) := by
    change mixedMoment B node4257 node4257Labels = _
    exact sound4257 B hB hF
  have h4514 : mixedVector B (Sum.inr 4514) = Sparse.eval nodeValue4514 (mixedVector B) := by
    change mixedMoment B node4514 node4514Labels = _
    exact sound4514 B hB hF
  have h4519 : mixedVector B (Sum.inr 4519) = Sparse.eval nodeValue4519 (mixedVector B) := by
    change mixedMoment B node4519 node4519Labels = _
    exact sound4519 B hB hF
  have h4521 : mixedVector B (Sum.inr 4521) = Sparse.eval nodeValue4521 (mixedVector B) := by
    change mixedMoment B node4521 node4521Labels = _
    exact sound4521 B hB hF
  have h4525 : mixedVector B (Sum.inr 4525) = Sparse.eval nodeValue4525 (mixedVector B) := by
    change mixedMoment B node4525 node4525Labels = _
    exact sound4525 B hB hF
  have h4543 : mixedVector B (Sum.inr 4543) = Sparse.eval nodeValue4543 (mixedVector B) := by
    change mixedMoment B node4543 node4543Labels = _
    exact sound4543 B hB hF
  have h4583 : mixedVector B (Sum.inr 4583) = Sparse.eval nodeValue4583 (mixedVector B) := by
    change mixedMoment B node4583 node4583Labels = _
    exact sound4583 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  simpa only [sourceForm1303, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4140, h4142, h4147, h4174, h4202, h4225, h4257, h4514, h4519, h4521, h4525, h4543, h4583, h4602, h4605, h4612, h4623, h4807, h4843, h4890, h5294, reducedSource1130] using sourceEq1303 B hB

theorem rowSound1130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1130 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1130, numericCheck1130, reducedZero1130 B hB hF, mul_zero]

theorem reducedZero1131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1131 (mixedVector B) = 0 := by
  have h568 : mixedVector B (Sum.inr 568) = Sparse.eval nodeValue568 (mixedVector B) := by
    change mixedMoment B node568 node568Labels = _
    exact sound568 B hB hF
  have h570 : mixedVector B (Sum.inr 570) = Sparse.eval nodeValue570 (mixedVector B) := by
    change mixedMoment B node570 node570Labels = _
    exact sound570 B hB hF
  have h575 : mixedVector B (Sum.inr 575) = Sparse.eval nodeValue575 (mixedVector B) := by
    change mixedMoment B node575 node575Labels = _
    exact sound575 B hB hF
  have h602 : mixedVector B (Sum.inr 602) = Sparse.eval nodeValue602 (mixedVector B) := by
    change mixedMoment B node602 node602Labels = _
    exact sound602 B hB hF
  have h705 : mixedVector B (Sum.inr 705) = Sparse.eval nodeValue705 (mixedVector B) := by
    change mixedMoment B node705 node705Labels = _
    exact sound705 B hB hF
  have h726 : mixedVector B (Sum.inr 726) = Sparse.eval nodeValue726 (mixedVector B) := by
    change mixedMoment B node726 node726Labels = _
    exact sound726 B hB hF
  have h791 : mixedVector B (Sum.inr 791) = Sparse.eval nodeValue791 (mixedVector B) := by
    change mixedMoment B node791 node791Labels = _
    exact sound791 B hB hF
  have h1098 : mixedVector B (Sum.inr 1098) = Sparse.eval nodeValue1098 (mixedVector B) := by
    change mixedMoment B node1098 node1098Labels = _
    exact sound1098 B hB hF
  have h1103 : mixedVector B (Sum.inr 1103) = Sparse.eval nodeValue1103 (mixedVector B) := by
    change mixedMoment B node1103 node1103Labels = _
    exact sound1103 B hB hF
  have h1105 : mixedVector B (Sum.inr 1105) = Sparse.eval nodeValue1105 (mixedVector B) := by
    change mixedMoment B node1105 node1105Labels = _
    exact sound1105 B hB hF
  have h1109 : mixedVector B (Sum.inr 1109) = Sparse.eval nodeValue1109 (mixedVector B) := by
    change mixedMoment B node1109 node1109Labels = _
    exact sound1109 B hB hF
  have h1128 : mixedVector B (Sum.inr 1128) = Sparse.eval nodeValue1128 (mixedVector B) := by
    change mixedMoment B node1128 node1128Labels = _
    exact sound1128 B hB hF
  have h1202 : mixedVector B (Sum.inr 1202) = Sparse.eval nodeValue1202 (mixedVector B) := by
    change mixedMoment B node1202 node1202Labels = _
    exact sound1202 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h1300 : mixedVector B (Sum.inr 1300) = Sparse.eval nodeValue1300 (mixedVector B) := by
    change mixedMoment B node1300 node1300Labels = _
    exact sound1300 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  simpa only [sourceForm1304, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h568, h570, h575, h602, h705, h726, h791, h1098, h1103, h1105, h1109, h1128, h1202, h1236, h1239, h1246, h1300, h2025, h2062, h2247, h3101, reducedSource1131] using sourceEq1304 B hB

theorem rowSound1131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1131 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1131, numericCheck1131, reducedZero1131 B hB hF, mul_zero]

theorem reducedZero1132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1132 (mixedVector B) = 0 := by
  have h1002 : mixedVector B (Sum.inr 1002) = Sparse.eval nodeValue1002 (mixedVector B) := by
    change mixedMoment B node1002 node1002Labels = _
    exact sound1002 B hB hF
  have h1599 : mixedVector B (Sum.inr 1599) = Sparse.eval nodeValue1599 (mixedVector B) := by
    change mixedMoment B node1599 node1599Labels = _
    exact sound1599 B hB hF
  have h1625 : mixedVector B (Sum.inr 1625) = Sparse.eval nodeValue1625 (mixedVector B) := by
    change mixedMoment B node1625 node1625Labels = _
    exact sound1625 B hB hF
  have h1730 : mixedVector B (Sum.inr 1730) = Sparse.eval nodeValue1730 (mixedVector B) := by
    change mixedMoment B node1730 node1730Labels = _
    exact sound1730 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1307, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1002, h1599, h1625, h1730, h2226, h4070, reducedSource1132] using sourceEq1307 B hB

theorem rowSound1132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1132 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1132, numericCheck1132, reducedZero1132 B hB hF, mul_zero]

theorem reducedZero1133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1133 (mixedVector B) = 0 := by
  have h1231 : mixedVector B (Sum.inr 1231) = Sparse.eval nodeValue1231 (mixedVector B) := by
    change mixedMoment B node1231 node1231Labels = _
    exact sound1231 B hB hF
  have h1637 : mixedVector B (Sum.inr 1637) = Sparse.eval nodeValue1637 (mixedVector B) := by
    change mixedMoment B node1637 node1637Labels = _
    exact sound1637 B hB hF
  have h1650 : mixedVector B (Sum.inr 1650) = Sparse.eval nodeValue1650 (mixedVector B) := by
    change mixedMoment B node1650 node1650Labels = _
    exact sound1650 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1308, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1231, h1637, h1650, h1710, h2737, h4069, reducedSource1133] using sourceEq1308 B hB

theorem rowSound1133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1133 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1133, numericCheck1133, reducedZero1133 B hB hF, mul_zero]

theorem reducedZero1134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1134 (mixedVector B) = 0 := by
  have h1191 : mixedVector B (Sum.inr 1191) = Sparse.eval nodeValue1191 (mixedVector B) := by
    change mixedMoment B node1191 node1191Labels = _
    exact sound1191 B hB hF
  have h2391 : mixedVector B (Sum.inr 2391) = Sparse.eval nodeValue2391 (mixedVector B) := by
    change mixedMoment B node2391 node2391Labels = _
    exact sound2391 B hB hF
  have h2407 : mixedVector B (Sum.inr 2407) = Sparse.eval nodeValue2407 (mixedVector B) := by
    change mixedMoment B node2407 node2407Labels = _
    exact sound2407 B hB hF
  have h2680 : mixedVector B (Sum.inr 2680) = Sparse.eval nodeValue2680 (mixedVector B) := by
    change mixedMoment B node2680 node2680Labels = _
    exact sound2680 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm1309, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1191, h2391, h2407, h2680, h2686, h4089, reducedSource1134] using sourceEq1309 B hB

theorem rowSound1134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1134 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1134, numericCheck1134, reducedZero1134 B hB hF, mul_zero]

theorem reducedZero1135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1135 (mixedVector B) = 0 := by
  have h1185 : mixedVector B (Sum.inr 1185) = Sparse.eval nodeValue1185 (mixedVector B) := by
    change mixedMoment B node1185 node1185Labels = _
    exact sound1185 B hB hF
  have h1191 : mixedVector B (Sum.inr 1191) = Sparse.eval nodeValue1191 (mixedVector B) := by
    change mixedMoment B node1191 node1191Labels = _
    exact sound1191 B hB hF
  have h1193 : mixedVector B (Sum.inr 1193) = Sparse.eval nodeValue1193 (mixedVector B) := by
    change mixedMoment B node1193 node1193Labels = _
    exact sound1193 B hB hF
  have h1288 : mixedVector B (Sum.inr 1288) = Sparse.eval nodeValue1288 (mixedVector B) := by
    change mixedMoment B node1288 node1288Labels = _
    exact sound1288 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm1310, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1185, h1191, h1193, h1288, h2686, h4089, reducedSource1135] using sourceEq1310 B hB

theorem rowSound1135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1135 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1135, numericCheck1135, reducedZero1135 B hB hF, mul_zero]

theorem sourceRowsAt1120 : MixedData.sourceRows (1120 : Fin 2425) =
    MixedData.row1120 := by decide +kernel

theorem sourceRowsAt1121 : MixedData.sourceRows (1121 : Fin 2425) =
    MixedData.row1121 := by decide +kernel

theorem sourceRowsAt1122 : MixedData.sourceRows (1122 : Fin 2425) =
    MixedData.row1122 := by decide +kernel

theorem sourceRowsAt1123 : MixedData.sourceRows (1123 : Fin 2425) =
    MixedData.row1123 := by decide +kernel

theorem sourceRowsAt1124 : MixedData.sourceRows (1124 : Fin 2425) =
    MixedData.row1124 := by decide +kernel

theorem sourceRowsAt1125 : MixedData.sourceRows (1125 : Fin 2425) =
    MixedData.row1125 := by decide +kernel

theorem sourceRowsAt1126 : MixedData.sourceRows (1126 : Fin 2425) =
    MixedData.row1126 := by decide +kernel

theorem sourceRowsAt1127 : MixedData.sourceRows (1127 : Fin 2425) =
    MixedData.row1127 := by decide +kernel

theorem sourceRowsAt1128 : MixedData.sourceRows (1128 : Fin 2425) =
    MixedData.row1128 := by decide +kernel

theorem sourceRowsAt1129 : MixedData.sourceRows (1129 : Fin 2425) =
    MixedData.row1129 := by decide +kernel

theorem sourceRowsAt1130 : MixedData.sourceRows (1130 : Fin 2425) =
    MixedData.row1130 := by decide +kernel

theorem sourceRowsAt1131 : MixedData.sourceRows (1131 : Fin 2425) =
    MixedData.row1131 := by decide +kernel

theorem sourceRowsAt1132 : MixedData.sourceRows (1132 : Fin 2425) =
    MixedData.row1132 := by decide +kernel

theorem sourceRowsAt1133 : MixedData.sourceRows (1133 : Fin 2425) =
    MixedData.row1133 := by decide +kernel

theorem sourceRowsAt1134 : MixedData.sourceRows (1134 : Fin 2425) =
    MixedData.row1134 := by decide +kernel

theorem sourceRowsAt1135 : MixedData.sourceRows (1135 : Fin 2425) =
    MixedData.row1135 := by decide +kernel

theorem chunkSound70 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 70) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1120 ∨ k.val = 1121 ∨ k.val = 1122 ∨ k.val = 1123 ∨ k.val = 1124 ∨ k.val = 1125 ∨ k.val = 1126 ∨ k.val = 1127 ∨ k.val = 1128 ∨ k.val = 1129 ∨ k.val = 1130 ∨ k.val = 1131 ∨ k.val = 1132 ∨ k.val = 1133 ∨ k.val = 1134 ∨ k.val = 1135 := by omega
  rcases heq with h1120 | h1121 | h1122 | h1123 | h1124 | h1125 | h1126 | h1127 | h1128 | h1129 | h1130 | h1131 | h1132 | h1133 | h1134 | h1135
  · have he : k = (1120 : Fin 2425) := Fin.ext h1120
    subst k
    rw [sourceRowsAt1120]
    exact rowSound1120 B hB hF
  · have he : k = (1121 : Fin 2425) := Fin.ext h1121
    subst k
    rw [sourceRowsAt1121]
    exact rowSound1121 B hB hF
  · have he : k = (1122 : Fin 2425) := Fin.ext h1122
    subst k
    rw [sourceRowsAt1122]
    exact rowSound1122 B hB hF
  · have he : k = (1123 : Fin 2425) := Fin.ext h1123
    subst k
    rw [sourceRowsAt1123]
    exact rowSound1123 B hB hF
  · have he : k = (1124 : Fin 2425) := Fin.ext h1124
    subst k
    rw [sourceRowsAt1124]
    exact rowSound1124 B hB hF
  · have he : k = (1125 : Fin 2425) := Fin.ext h1125
    subst k
    rw [sourceRowsAt1125]
    exact rowSound1125 B hB hF
  · have he : k = (1126 : Fin 2425) := Fin.ext h1126
    subst k
    rw [sourceRowsAt1126]
    exact rowSound1126 B hB hF
  · have he : k = (1127 : Fin 2425) := Fin.ext h1127
    subst k
    rw [sourceRowsAt1127]
    exact rowSound1127 B hB hF
  · have he : k = (1128 : Fin 2425) := Fin.ext h1128
    subst k
    rw [sourceRowsAt1128]
    exact rowSound1128 B hB hF
  · have he : k = (1129 : Fin 2425) := Fin.ext h1129
    subst k
    rw [sourceRowsAt1129]
    exact rowSound1129 B hB hF
  · have he : k = (1130 : Fin 2425) := Fin.ext h1130
    subst k
    rw [sourceRowsAt1130]
    exact rowSound1130 B hB hF
  · have he : k = (1131 : Fin 2425) := Fin.ext h1131
    subst k
    rw [sourceRowsAt1131]
    exact rowSound1131 B hB hF
  · have he : k = (1132 : Fin 2425) := Fin.ext h1132
    subst k
    rw [sourceRowsAt1132]
    exact rowSound1132 B hB hF
  · have he : k = (1133 : Fin 2425) := Fin.ext h1133
    subst k
    rw [sourceRowsAt1133]
    exact rowSound1133 B hB hF
  · have he : k = (1134 : Fin 2425) := Fin.ext h1134
    subst k
    rw [sourceRowsAt1134]
    exact rowSound1134 B hB hF
  · have he : k = (1135 : Fin 2425) := Fin.ext h1135
    subst k
    rw [sourceRowsAt1135]
    exact rowSound1135 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
