import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources39

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1072 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1072 (mixedVector B) = 0 := by
  have h1619 : mixedVector B (Sum.inr 1619) = Sparse.eval nodeValue1619 (mixedVector B) := by
    change mixedMoment B node1619 node1619Labels = _
    exact sound1619 B hB hF
  have h1628 : mixedVector B (Sum.inr 1628) = Sparse.eval nodeValue1628 (mixedVector B) := by
    change mixedMoment B node1628 node1628Labels = _
    exact sound1628 B hB hF
  have h1630 : mixedVector B (Sum.inr 1630) = Sparse.eval nodeValue1630 (mixedVector B) := by
    change mixedMoment B node1630 node1630Labels = _
    exact sound1630 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1241, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1619, h1628, h1630, h1756, h3302, h4070, reducedSource1072] using sourceEq1241 B hB

theorem rowSound1072 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1072 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1072, numericCheck1072, reducedZero1072 B hB hF, mul_zero]

theorem reducedZero1073 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1073 (mixedVector B) = 0 := by
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3310 : mixedVector B (Sum.inr 3310) = Sparse.eval nodeValue3310 (mixedVector B) := by
    change mixedMoment B node3310 node3310Labels = _
    exact sound3310 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1242, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1756, h2289, h3302, h3310, h4070, reducedSource1073] using sourceEq1242 B hB

theorem rowSound1073 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1073 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1073, numericCheck1073, reducedZero1073 B hB hF, mul_zero]

theorem reducedZero1074 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1074 (mixedVector B) = 0 := by
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3310 : mixedVector B (Sum.inr 3310) = Sparse.eval nodeValue3310 (mixedVector B) := by
    change mixedMoment B node3310 node3310Labels = _
    exact sound3310 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1243, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1725, h3291, h3300, h3302, h3310, h4070, reducedSource1074] using sourceEq1243 B hB

theorem rowSound1074 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1074 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1074, numericCheck1074, reducedZero1074 B hB hF, mul_zero]

theorem reducedZero1075 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1075 (mixedVector B) = 0 := by
  have h1630 : mixedVector B (Sum.inr 1630) = Sparse.eval nodeValue1630 (mixedVector B) := by
    change mixedMoment B node1630 node1630Labels = _
    exact sound1630 B hB hF
  have h3247 : mixedVector B (Sum.inr 3247) = Sparse.eval nodeValue3247 (mixedVector B) := by
    change mixedMoment B node3247 node3247Labels = _
    exact sound3247 B hB hF
  have h3283 : mixedVector B (Sum.inr 3283) = Sparse.eval nodeValue3283 (mixedVector B) := by
    change mixedMoment B node3283 node3283Labels = _
    exact sound3283 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1244, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1630, h3247, h3283, h3300, h3302, h4070, reducedSource1075] using sourceEq1244 B hB

theorem rowSound1075 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1075 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1075, numericCheck1075, reducedZero1075 B hB hF, mul_zero]

theorem reducedZero1076 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1076 (mixedVector B) = 0 := by
  have h1258 : mixedVector B (Sum.inr 1258) = Sparse.eval nodeValue1258 (mixedVector B) := by
    change mixedMoment B node1258 node1258Labels = _
    exact sound1258 B hB hF
  have h2119 : mixedVector B (Sum.inr 2119) = Sparse.eval nodeValue2119 (mixedVector B) := by
    change mixedMoment B node2119 node2119Labels = _
    exact sound2119 B hB hF
  have h2130 : mixedVector B (Sum.inr 2130) = Sparse.eval nodeValue2130 (mixedVector B) := by
    change mixedMoment B node2130 node2130Labels = _
    exact sound2130 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2761 : mixedVector B (Sum.inr 2761) = Sparse.eval nodeValue2761 (mixedVector B) := by
    change mixedMoment B node2761 node2761Labels = _
    exact sound2761 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1246, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1258, h2119, h2130, h2218, h2761, h4082, reducedSource1076] using sourceEq1246 B hB

theorem rowSound1076 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1076 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1076, numericCheck1076, reducedZero1076 B hB hF, mul_zero]

theorem reducedZero1077 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1077 (mixedVector B) = 0 := by
  have h1111 : mixedVector B (Sum.inr 1111) = Sparse.eval nodeValue1111 (mixedVector B) := by
    change mixedMoment B node1111 node1111Labels = _
    exact sound1111 B hB hF
  have h1115 : mixedVector B (Sum.inr 1115) = Sparse.eval nodeValue1115 (mixedVector B) := by
    change mixedMoment B node1115 node1115Labels = _
    exact sound1115 B hB hF
  have h1119 : mixedVector B (Sum.inr 1119) = Sparse.eval nodeValue1119 (mixedVector B) := by
    change mixedMoment B node1119 node1119Labels = _
    exact sound1119 B hB hF
  have h1131 : mixedVector B (Sum.inr 1131) = Sparse.eval nodeValue1131 (mixedVector B) := by
    change mixedMoment B node1131 node1131Labels = _
    exact sound1131 B hB hF
  have h1215 : mixedVector B (Sum.inr 1215) = Sparse.eval nodeValue1215 (mixedVector B) := by
    change mixedMoment B node1215 node1215Labels = _
    exact sound1215 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1247, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1111, h1115, h1119, h1131, h1215, h2482, h4092, reducedSource1077] using sourceEq1247 B hB

theorem rowSound1077 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1077 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1077, numericCheck1077, reducedZero1077 B hB hF, mul_zero]

theorem reducedZero1078 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1078 (mixedVector B) = 0 := by
  have h626 : mixedVector B (Sum.inr 626) = Sparse.eval nodeValue626 (mixedVector B) := by
    change mixedMoment B node626 node626Labels = _
    exact sound626 B hB hF
  have h1131 : mixedVector B (Sum.inr 1131) = Sparse.eval nodeValue1131 (mixedVector B) := by
    change mixedMoment B node1131 node1131Labels = _
    exact sound1131 B hB hF
  have h1148 : mixedVector B (Sum.inr 1148) = Sparse.eval nodeValue1148 (mixedVector B) := by
    change mixedMoment B node1148 node1148Labels = _
    exact sound1148 B hB hF
  have h1215 : mixedVector B (Sum.inr 1215) = Sparse.eval nodeValue1215 (mixedVector B) := by
    change mixedMoment B node1215 node1215Labels = _
    exact sound1215 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1248, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h626, h1131, h1148, h1215, h1236, h1242, h4092, reducedSource1078] using sourceEq1248 B hB

theorem rowSound1078 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1078 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1078, numericCheck1078, reducedZero1078 B hB hF, mul_zero]

theorem reducedZero1079 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1079 (mixedVector B) = 0 := by
  have h630 : mixedVector B (Sum.inr 630) = Sparse.eval nodeValue630 (mixedVector B) := by
    change mixedMoment B node630 node630Labels = _
    exact sound630 B hB hF
  have h1136 : mixedVector B (Sum.inr 1136) = Sparse.eval nodeValue1136 (mixedVector B) := by
    change mixedMoment B node1136 node1136Labels = _
    exact sound1136 B hB hF
  have h1150 : mixedVector B (Sum.inr 1150) = Sparse.eval nodeValue1150 (mixedVector B) := by
    change mixedMoment B node1150 node1150Labels = _
    exact sound1150 B hB hF
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1249, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h630, h1136, h1150, h1217, h1240, h4091, reducedSource1079] using sourceEq1249 B hB

theorem rowSound1079 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1079 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1079, numericCheck1079, reducedZero1079 B hB hF, mul_zero]

theorem reducedZero1080 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1080 (mixedVector B) = 0 := by
  have h1112 : mixedVector B (Sum.inr 1112) = Sparse.eval nodeValue1112 (mixedVector B) := by
    change mixedMoment B node1112 node1112Labels = _
    exact sound1112 B hB hF
  have h1118 : mixedVector B (Sum.inr 1118) = Sparse.eval nodeValue1118 (mixedVector B) := by
    change mixedMoment B node1118 node1118Labels = _
    exact sound1118 B hB hF
  have h1120 : mixedVector B (Sum.inr 1120) = Sparse.eval nodeValue1120 (mixedVector B) := by
    change mixedMoment B node1120 node1120Labels = _
    exact sound1120 B hB hF
  have h1136 : mixedVector B (Sum.inr 1136) = Sparse.eval nodeValue1136 (mixedVector B) := by
    change mixedMoment B node1136 node1136Labels = _
    exact sound1136 B hB hF
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1250, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1112, h1118, h1120, h1136, h1217, h2485, h4091, reducedSource1080] using sourceEq1250 B hB

theorem rowSound1080 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1080 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1080, numericCheck1080, reducedZero1080 B hB hF, mul_zero]

theorem reducedZero1081 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1081 (mixedVector B) = 0 := by
  have h1613 : mixedVector B (Sum.inr 1613) = Sparse.eval nodeValue1613 (mixedVector B) := by
    change mixedMoment B node1613 node1613Labels = _
    exact sound1613 B hB hF
  have h1617 : mixedVector B (Sum.inr 1617) = Sparse.eval nodeValue1617 (mixedVector B) := by
    change mixedMoment B node1617 node1617Labels = _
    exact sound1617 B hB hF
  have h1619 : mixedVector B (Sum.inr 1619) = Sparse.eval nodeValue1619 (mixedVector B) := by
    change mixedMoment B node1619 node1619Labels = _
    exact sound1619 B hB hF
  have h1624 : mixedVector B (Sum.inr 1624) = Sparse.eval nodeValue1624 (mixedVector B) := by
    change mixedMoment B node1624 node1624Labels = _
    exact sound1624 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1251, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1613, h1617, h1619, h1624, h1750, h3291, h4070, reducedSource1081] using sourceEq1251 B hB

theorem rowSound1081 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1081 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1081, numericCheck1081, reducedZero1081 B hB hF, mul_zero]

theorem reducedZero1082 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1082 (mixedVector B) = 0 := by
  have h1596 : mixedVector B (Sum.inr 1596) = Sparse.eval nodeValue1596 (mixedVector B) := by
    change mixedMoment B node1596 node1596Labels = _
    exact sound1596 B hB hF
  have h1599 : mixedVector B (Sum.inr 1599) = Sparse.eval nodeValue1599 (mixedVector B) := by
    change mixedMoment B node1599 node1599Labels = _
    exact sound1599 B hB hF
  have h1604 : mixedVector B (Sum.inr 1604) = Sparse.eval nodeValue1604 (mixedVector B) := by
    change mixedMoment B node1604 node1604Labels = _
    exact sound1604 B hB hF
  have h1617 : mixedVector B (Sum.inr 1617) = Sparse.eval nodeValue1617 (mixedVector B) := by
    change mixedMoment B node1617 node1617Labels = _
    exact sound1617 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1252, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1596, h1599, h1604, h1617, h1725, h3291, h4070, reducedSource1082] using sourceEq1252 B hB

theorem rowSound1082 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1082 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1082, numericCheck1082, reducedZero1082 B hB hF, mul_zero]

theorem reducedZero1083 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1083 (mixedVector B) = 0 := by
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3310 : mixedVector B (Sum.inr 3310) = Sparse.eval nodeValue3310 (mixedVector B) := by
    change mixedMoment B node3310 node3310Labels = _
    exact sound3310 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1253, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1750, h2226, h3291, h3300, h3310, h4070, reducedSource1083] using sourceEq1253 B hB

theorem rowSound1083 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1083 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1083, numericCheck1083, reducedZero1083 B hB hF, mul_zero]

theorem reducedZero1084 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1084 (mixedVector B) = 0 := by
  have h1617 : mixedVector B (Sum.inr 1617) = Sparse.eval nodeValue1617 (mixedVector B) := by
    change mixedMoment B node1617 node1617Labels = _
    exact sound1617 B hB hF
  have h3242 : mixedVector B (Sum.inr 3242) = Sparse.eval nodeValue3242 (mixedVector B) := by
    change mixedMoment B node3242 node3242Labels = _
    exact sound3242 B hB hF
  have h3279 : mixedVector B (Sum.inr 3279) = Sparse.eval nodeValue3279 (mixedVector B) := by
    change mixedMoment B node3279 node3279Labels = _
    exact sound3279 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1254, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1617, h3242, h3279, h3291, h3300, h4070, reducedSource1084] using sourceEq1254 B hB

theorem rowSound1084 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1084 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1084, numericCheck1084, reducedZero1084 B hB hF, mul_zero]

theorem reducedZero1085 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1085 (mixedVector B) = 0 := by
  have h1599 : mixedVector B (Sum.inr 1599) = Sparse.eval nodeValue1599 (mixedVector B) := by
    change mixedMoment B node1599 node1599Labels = _
    exact sound1599 B hB hF
  have h1995 : mixedVector B (Sum.inr 1995) = Sparse.eval nodeValue1995 (mixedVector B) := by
    change mixedMoment B node1995 node1995Labels = _
    exact sound1995 B hB hF
  have h2005 : mixedVector B (Sum.inr 2005) = Sparse.eval nodeValue2005 (mixedVector B) := by
    change mixedMoment B node2005 node2005Labels = _
    exact sound2005 B hB hF
  have h2045 : mixedVector B (Sum.inr 2045) = Sparse.eval nodeValue2045 (mixedVector B) := by
    change mixedMoment B node2045 node2045Labels = _
    exact sound2045 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1255, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1599, h1995, h2005, h2045, h2226, h3291, h4070, reducedSource1085] using sourceEq1255 B hB

theorem rowSound1085 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1085 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1085, numericCheck1085, reducedZero1085 B hB hF, mul_zero]

theorem reducedZero1086 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1086 (mixedVector B) = 0 := by
  have h1211 : mixedVector B (Sum.inr 1211) = Sparse.eval nodeValue1211 (mixedVector B) := by
    change mixedMoment B node1211 node1211Labels = _
    exact sound1211 B hB hF
  have h2070 : mixedVector B (Sum.inr 2070) = Sparse.eval nodeValue2070 (mixedVector B) := by
    change mixedMoment B node2070 node2070Labels = _
    exact sound2070 B hB hF
  have h2079 : mixedVector B (Sum.inr 2079) = Sparse.eval nodeValue2079 (mixedVector B) := by
    change mixedMoment B node2079 node2079Labels = _
    exact sound2079 B hB hF
  have h2087 : mixedVector B (Sum.inr 2087) = Sparse.eval nodeValue2087 (mixedVector B) := by
    change mixedMoment B node2087 node2087Labels = _
    exact sound2087 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1256, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1211, h2070, h2079, h2087, h2193, h2719, h4080, reducedSource1086] using sourceEq1256 B hB

theorem rowSound1086 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1086 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1086, numericCheck1086, reducedZero1086 B hB hF, mul_zero]

theorem reducedZero1087 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1087 (mixedVector B) = 0 := by
  have h1181 : mixedVector B (Sum.inr 1181) = Sparse.eval nodeValue1181 (mixedVector B) := by
    change mixedMoment B node1181 node1181Labels = _
    exact sound1181 B hB hF
  have h2385 : mixedVector B (Sum.inr 2385) = Sparse.eval nodeValue2385 (mixedVector B) := by
    change mixedMoment B node2385 node2385Labels = _
    exact sound2385 B hB hF
  have h2453 : mixedVector B (Sum.inr 2453) = Sparse.eval nodeValue2453 (mixedVector B) := by
    change mixedMoment B node2453 node2453Labels = _
    exact sound2453 B hB hF
  have h2492 : mixedVector B (Sum.inr 2492) = Sparse.eval nodeValue2492 (mixedVector B) := by
    change mixedMoment B node2492 node2492Labels = _
    exact sound2492 B hB hF
  have h2664 : mixedVector B (Sum.inr 2664) = Sparse.eval nodeValue2664 (mixedVector B) := by
    change mixedMoment B node2664 node2664Labels = _
    exact sound2664 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1257, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1181, h2385, h2453, h2492, h2664, h2672, h4088, reducedSource1087] using sourceEq1257 B hB

theorem rowSound1087 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1087 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1087, numericCheck1087, reducedZero1087 B hB hF, mul_zero]

theorem sourceRowsAt1072 : MixedData.sourceRows (1072 : Fin 2425) =
    MixedData.row1072 := by decide +kernel

theorem sourceRowsAt1073 : MixedData.sourceRows (1073 : Fin 2425) =
    MixedData.row1073 := by decide +kernel

theorem sourceRowsAt1074 : MixedData.sourceRows (1074 : Fin 2425) =
    MixedData.row1074 := by decide +kernel

theorem sourceRowsAt1075 : MixedData.sourceRows (1075 : Fin 2425) =
    MixedData.row1075 := by decide +kernel

theorem sourceRowsAt1076 : MixedData.sourceRows (1076 : Fin 2425) =
    MixedData.row1076 := by decide +kernel

theorem sourceRowsAt1077 : MixedData.sourceRows (1077 : Fin 2425) =
    MixedData.row1077 := by decide +kernel

theorem sourceRowsAt1078 : MixedData.sourceRows (1078 : Fin 2425) =
    MixedData.row1078 := by decide +kernel

theorem sourceRowsAt1079 : MixedData.sourceRows (1079 : Fin 2425) =
    MixedData.row1079 := by decide +kernel

theorem sourceRowsAt1080 : MixedData.sourceRows (1080 : Fin 2425) =
    MixedData.row1080 := by decide +kernel

theorem sourceRowsAt1081 : MixedData.sourceRows (1081 : Fin 2425) =
    MixedData.row1081 := by decide +kernel

theorem sourceRowsAt1082 : MixedData.sourceRows (1082 : Fin 2425) =
    MixedData.row1082 := by decide +kernel

theorem sourceRowsAt1083 : MixedData.sourceRows (1083 : Fin 2425) =
    MixedData.row1083 := by decide +kernel

theorem sourceRowsAt1084 : MixedData.sourceRows (1084 : Fin 2425) =
    MixedData.row1084 := by decide +kernel

theorem sourceRowsAt1085 : MixedData.sourceRows (1085 : Fin 2425) =
    MixedData.row1085 := by decide +kernel

theorem sourceRowsAt1086 : MixedData.sourceRows (1086 : Fin 2425) =
    MixedData.row1086 := by decide +kernel

theorem sourceRowsAt1087 : MixedData.sourceRows (1087 : Fin 2425) =
    MixedData.row1087 := by decide +kernel

theorem chunkSound67 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 67) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1072 ∨ k.val = 1073 ∨ k.val = 1074 ∨ k.val = 1075 ∨ k.val = 1076 ∨ k.val = 1077 ∨ k.val = 1078 ∨ k.val = 1079 ∨ k.val = 1080 ∨ k.val = 1081 ∨ k.val = 1082 ∨ k.val = 1083 ∨ k.val = 1084 ∨ k.val = 1085 ∨ k.val = 1086 ∨ k.val = 1087 := by omega
  rcases heq with h1072 | h1073 | h1074 | h1075 | h1076 | h1077 | h1078 | h1079 | h1080 | h1081 | h1082 | h1083 | h1084 | h1085 | h1086 | h1087
  · have he : k = (1072 : Fin 2425) := Fin.ext h1072
    subst k
    rw [sourceRowsAt1072]
    exact rowSound1072 B hB hF
  · have he : k = (1073 : Fin 2425) := Fin.ext h1073
    subst k
    rw [sourceRowsAt1073]
    exact rowSound1073 B hB hF
  · have he : k = (1074 : Fin 2425) := Fin.ext h1074
    subst k
    rw [sourceRowsAt1074]
    exact rowSound1074 B hB hF
  · have he : k = (1075 : Fin 2425) := Fin.ext h1075
    subst k
    rw [sourceRowsAt1075]
    exact rowSound1075 B hB hF
  · have he : k = (1076 : Fin 2425) := Fin.ext h1076
    subst k
    rw [sourceRowsAt1076]
    exact rowSound1076 B hB hF
  · have he : k = (1077 : Fin 2425) := Fin.ext h1077
    subst k
    rw [sourceRowsAt1077]
    exact rowSound1077 B hB hF
  · have he : k = (1078 : Fin 2425) := Fin.ext h1078
    subst k
    rw [sourceRowsAt1078]
    exact rowSound1078 B hB hF
  · have he : k = (1079 : Fin 2425) := Fin.ext h1079
    subst k
    rw [sourceRowsAt1079]
    exact rowSound1079 B hB hF
  · have he : k = (1080 : Fin 2425) := Fin.ext h1080
    subst k
    rw [sourceRowsAt1080]
    exact rowSound1080 B hB hF
  · have he : k = (1081 : Fin 2425) := Fin.ext h1081
    subst k
    rw [sourceRowsAt1081]
    exact rowSound1081 B hB hF
  · have he : k = (1082 : Fin 2425) := Fin.ext h1082
    subst k
    rw [sourceRowsAt1082]
    exact rowSound1082 B hB hF
  · have he : k = (1083 : Fin 2425) := Fin.ext h1083
    subst k
    rw [sourceRowsAt1083]
    exact rowSound1083 B hB hF
  · have he : k = (1084 : Fin 2425) := Fin.ext h1084
    subst k
    rw [sourceRowsAt1084]
    exact rowSound1084 B hB hF
  · have he : k = (1085 : Fin 2425) := Fin.ext h1085
    subst k
    rw [sourceRowsAt1085]
    exact rowSound1085 B hB hF
  · have he : k = (1086 : Fin 2425) := Fin.ext h1086
    subst k
    rw [sourceRowsAt1086]
    exact rowSound1086 B hB hF
  · have he : k = (1087 : Fin 2425) := Fin.ext h1087
    subst k
    rw [sourceRowsAt1087]
    exact rowSound1087 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
