import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic86
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources50

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1376 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1376 (mixedVector B) = 0 := by
  have h1598 : mixedVector B (Sum.inr 1598) = Sparse.eval nodeValue1598 (mixedVector B) := by
    change mixedMoment B node1598 node1598Labels = _
    exact sound1598 B hB hF
  have h1603 : mixedVector B (Sum.inr 1603) = Sparse.eval nodeValue1603 (mixedVector B) := by
    change mixedMoment B node1603 node1603Labels = _
    exact sound1603 B hB hF
  have h1605 : mixedVector B (Sum.inr 1605) = Sparse.eval nodeValue1605 (mixedVector B) := by
    change mixedMoment B node1605 node1605Labels = _
    exact sound1605 B hB hF
  have h1623 : mixedVector B (Sum.inr 1623) = Sparse.eval nodeValue1623 (mixedVector B) := by
    change mixedMoment B node1623 node1623Labels = _
    exact sound1623 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1615, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1598, h1603, h1605, h1623, h1728, h3294, h4069, reducedSource1376] using sourceEq1615 B hB

theorem rowSound1376 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1376 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1376, numericCheck1376, reducedZero1376 B hB hF, mul_zero]

theorem reducedZero1377 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1377 (mixedVector B) = 0 := by
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3306 : mixedVector B (Sum.inr 3306) = Sparse.eval nodeValue3306 (mixedVector B) := by
    change mixedMoment B node3306 node3306Labels = _
    exact sound3306 B hB hF
  have h3309 : mixedVector B (Sum.inr 3309) = Sparse.eval nodeValue3309 (mixedVector B) := by
    change mixedMoment B node3309 node3309Labels = _
    exact sound3309 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1616, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1728, h3294, h3305, h3306, h3309, h4069, reducedSource1377] using sourceEq1616 B hB

theorem rowSound1377 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1377 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1377, numericCheck1377, reducedZero1377 B hB hF, mul_zero]

theorem reducedZero1378 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1378 (mixedVector B) = 0 := by
  have h1623 : mixedVector B (Sum.inr 1623) = Sparse.eval nodeValue1623 (mixedVector B) := by
    change mixedMoment B node1623 node1623Labels = _
    exact sound1623 B hB hF
  have h3246 : mixedVector B (Sum.inr 3246) = Sparse.eval nodeValue3246 (mixedVector B) := by
    change mixedMoment B node3246 node3246Labels = _
    exact sound3246 B hB hF
  have h3282 : mixedVector B (Sum.inr 3282) = Sparse.eval nodeValue3282 (mixedVector B) := by
    change mixedMoment B node3282 node3282Labels = _
    exact sound3282 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1617, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1623, h3246, h3282, h3294, h3296, h3299, h4069, reducedSource1378] using sourceEq1617 B hB

theorem rowSound1378 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1378 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1378, numericCheck1378, reducedZero1378 B hB hF, mul_zero]

theorem reducedZero1379 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1379 (mixedVector B) = 0 := by
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h3309 : mixedVector B (Sum.inr 3309) = Sparse.eval nodeValue3309 (mixedVector B) := by
    change mixedMoment B node3309 node3309Labels = _
    exact sound3309 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1618, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1724, h3290, h3293, h3294, h3299, h3309, h4069, reducedSource1379] using sourceEq1618 B hB

theorem rowSound1379 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1379 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1379, numericCheck1379, reducedZero1379 B hB hF, mul_zero]

theorem reducedZero1380 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1380 (mixedVector B) = 0 := by
  have h1605 : mixedVector B (Sum.inr 1605) = Sparse.eval nodeValue1605 (mixedVector B) := by
    change mixedMoment B node1605 node1605Labels = _
    exact sound1605 B hB hF
  have h3240 : mixedVector B (Sum.inr 3240) = Sparse.eval nodeValue3240 (mixedVector B) := by
    change mixedMoment B node3240 node3240Labels = _
    exact sound3240 B hB hF
  have h3278 : mixedVector B (Sum.inr 3278) = Sparse.eval nodeValue3278 (mixedVector B) := by
    change mixedMoment B node3278 node3278Labels = _
    exact sound3278 B hB hF
  have h3287 : mixedVector B (Sum.inr 3287) = Sparse.eval nodeValue3287 (mixedVector B) := by
    change mixedMoment B node3287 node3287Labels = _
    exact sound3287 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1619, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1605, h3240, h3278, h3287, h3293, h3294, h4069, reducedSource1380] using sourceEq1619 B hB

theorem rowSound1380 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1380 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1380, numericCheck1380, reducedZero1380 B hB hF, mul_zero]

theorem reducedZero1381 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1381 (mixedVector B) = 0 := by
  have h1645 : mixedVector B (Sum.inr 1645) = Sparse.eval nodeValue1645 (mixedVector B) := by
    change mixedMoment B node1645 node1645Labels = _
    exact sound1645 B hB hF
  have h3022 : mixedVector B (Sum.inr 3022) = Sparse.eval nodeValue3022 (mixedVector B) := by
    change mixedMoment B node3022 node3022Labels = _
    exact sound3022 B hB hF
  have h3285 : mixedVector B (Sum.inr 3285) = Sparse.eval nodeValue3285 (mixedVector B) := by
    change mixedMoment B node3285 node3285Labels = _
    exact sound3285 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1620, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1645, h3022, h3285, h3294, h3296, h3305, h4069, reducedSource1381] using sourceEq1620 B hB

theorem rowSound1381 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1381 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1381, numericCheck1381, reducedZero1381 B hB hF, mul_zero]

theorem reducedZero1382 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1382 (mixedVector B) = 0 := by
  have h1257 : mixedVector B (Sum.inr 1257) = Sparse.eval nodeValue1257 (mixedVector B) := by
    change mixedMoment B node1257 node1257Labels = _
    exact sound1257 B hB hF
  have h2565 : mixedVector B (Sum.inr 2565) = Sparse.eval nodeValue2565 (mixedVector B) := by
    change mixedMoment B node2565 node2565Labels = _
    exact sound2565 B hB hF
  have h2629 : mixedVector B (Sum.inr 2629) = Sparse.eval nodeValue2629 (mixedVector B) := by
    change mixedMoment B node2629 node2629Labels = _
    exact sound2629 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h2748 : mixedVector B (Sum.inr 2748) = Sparse.eval nodeValue2748 (mixedVector B) := by
    change mixedMoment B node2748 node2748Labels = _
    exact sound2748 B hB hF
  have h2760 : mixedVector B (Sum.inr 2760) = Sparse.eval nodeValue2760 (mixedVector B) := by
    change mixedMoment B node2760 node2760Labels = _
    exact sound2760 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1621, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1257, h2565, h2629, h2672, h2748, h2760, h4088, reducedSource1382] using sourceEq1621 B hB

theorem rowSound1382 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1382 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1382, numericCheck1382, reducedZero1382 B hB hF, mul_zero]

theorem reducedZero1383 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1383 (mixedVector B) = 0 := by
  have h1130 : mixedVector B (Sum.inr 1130) = Sparse.eval nodeValue1130 (mixedVector B) := by
    change mixedMoment B node1130 node1130Labels = _
    exact sound1130 B hB hF
  have h1137 : mixedVector B (Sum.inr 1137) = Sparse.eval nodeValue1137 (mixedVector B) := by
    change mixedMoment B node1137 node1137Labels = _
    exact sound1137 B hB hF
  have h1138 : mixedVector B (Sum.inr 1138) = Sparse.eval nodeValue1138 (mixedVector B) := by
    change mixedMoment B node1138 node1138Labels = _
    exact sound1138 B hB hF
  have h1141 : mixedVector B (Sum.inr 1141) = Sparse.eval nodeValue1141 (mixedVector B) := by
    change mixedMoment B node1141 node1141Labels = _
    exact sound1141 B hB hF
  have h1241 : mixedVector B (Sum.inr 1241) = Sparse.eval nodeValue1241 (mixedVector B) := by
    change mixedMoment B node1241 node1241Labels = _
    exact sound1241 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1622, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1130, h1137, h1138, h1141, h1241, h2515, h4092, reducedSource1383] using sourceEq1622 B hB

theorem rowSound1383 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1383 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1383, numericCheck1383, reducedZero1383 B hB hF, mul_zero]

theorem reducedZero1384 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1384 (mixedVector B) = 0 := by
  have h638 : mixedVector B (Sum.inr 638) = Sparse.eval nodeValue638 (mixedVector B) := by
    change mixedMoment B node638 node638Labels = _
    exact sound638 B hB hF
  have h1156 : mixedVector B (Sum.inr 1156) = Sparse.eval nodeValue1156 (mixedVector B) := by
    change mixedMoment B node1156 node1156Labels = _
    exact sound1156 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1261 : mixedVector B (Sum.inr 1261) = Sparse.eval nodeValue1261 (mixedVector B) := by
    change mixedMoment B node1261 node1261Labels = _
    exact sound1261 B hB hF
  have h1291 : mixedVector B (Sum.inr 1291) = Sparse.eval nodeValue1291 (mixedVector B) := by
    change mixedMoment B node1291 node1291Labels = _
    exact sound1291 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1623, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h638, h1156, h1236, h1261, h1291, h1294, h4092, reducedSource1384] using sourceEq1623 B hB

theorem rowSound1384 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1384 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1384, numericCheck1384, reducedZero1384 B hB hF, mul_zero]

theorem reducedZero1385 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1385 (mixedVector B) = 0 := by
  have h1635 : mixedVector B (Sum.inr 1635) = Sparse.eval nodeValue1635 (mixedVector B) := by
    change mixedMoment B node1635 node1635Labels = _
    exact sound1635 B hB hF
  have h1637 : mixedVector B (Sum.inr 1637) = Sparse.eval nodeValue1637 (mixedVector B) := by
    change mixedMoment B node1637 node1637Labels = _
    exact sound1637 B hB hF
  have h1640 : mixedVector B (Sum.inr 1640) = Sparse.eval nodeValue1640 (mixedVector B) := by
    change mixedMoment B node1640 node1640Labels = _
    exact sound1640 B hB hF
  have h1645 : mixedVector B (Sum.inr 1645) = Sparse.eval nodeValue1645 (mixedVector B) := by
    change mixedMoment B node1645 node1645Labels = _
    exact sound1645 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1624, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1635, h1637, h1640, h1645, h1707, h3296, h4069, reducedSource1385] using sourceEq1624 B hB

theorem rowSound1385 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1385 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1385, numericCheck1385, reducedZero1385 B hB hF, mul_zero]

theorem reducedZero1386 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1386 (mixedVector B) = 0 := by
  have h1607 : mixedVector B (Sum.inr 1607) = Sparse.eval nodeValue1607 (mixedVector B) := by
    change mixedMoment B node1607 node1607Labels = _
    exact sound1607 B hB hF
  have h1610 : mixedVector B (Sum.inr 1610) = Sparse.eval nodeValue1610 (mixedVector B) := by
    change mixedMoment B node1610 node1610Labels = _
    exact sound1610 B hB hF
  have h1612 : mixedVector B (Sum.inr 1612) = Sparse.eval nodeValue1612 (mixedVector B) := by
    change mixedMoment B node1612 node1612Labels = _
    exact sound1612 B hB hF
  have h1623 : mixedVector B (Sum.inr 1623) = Sparse.eval nodeValue1623 (mixedVector B) := by
    change mixedMoment B node1623 node1623Labels = _
    exact sound1623 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1625, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1607, h1610, h1612, h1623, h1739, h3296, h4069, reducedSource1386] using sourceEq1625 B hB

theorem rowSound1386 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1386 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1386, numericCheck1386, reducedZero1386 B hB hF, mul_zero]

theorem reducedZero1387 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1387 (mixedVector B) = 0 := by
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3308 : mixedVector B (Sum.inr 3308) = Sparse.eval nodeValue3308 (mixedVector B) := by
    change mixedMoment B node3308 node3308Labels = _
    exact sound3308 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1626, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1739, h2737, h3296, h3305, h3308, h4069, reducedSource1387] using sourceEq1626 B hB

theorem rowSound1387 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1387 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1387, numericCheck1387, reducedZero1387 B hB hF, mul_zero]

theorem reducedZero1388 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1388 (mixedVector B) = 0 := by
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h3308 : mixedVector B (Sum.inr 3308) = Sparse.eval nodeValue3308 (mixedVector B) := by
    change mixedMoment B node3308 node3308Labels = _
    exact sound3308 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1627, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1707, h3288, h3296, h3299, h3308, h4069, reducedSource1388] using sourceEq1627 B hB

theorem rowSound1388 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1388 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1388, numericCheck1388, reducedZero1388 B hB hF, mul_zero]

theorem reducedZero1389 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1389 (mixedVector B) = 0 := by
  have h1111 : mixedVector B (Sum.inr 1111) = Sparse.eval nodeValue1111 (mixedVector B) := by
    change mixedMoment B node1111 node1111Labels = _
    exact sound1111 B hB hF
  have h1113 : mixedVector B (Sum.inr 1113) = Sparse.eval nodeValue1113 (mixedVector B) := by
    change mixedMoment B node1113 node1113Labels = _
    exact sound1113 B hB hF
  have h1126 : mixedVector B (Sum.inr 1126) = Sparse.eval nodeValue1126 (mixedVector B) := by
    change mixedMoment B node1126 node1126Labels = _
    exact sound1126 B hB hF
  have h1212 : mixedVector B (Sum.inr 1212) = Sparse.eval nodeValue1212 (mixedVector B) := by
    change mixedMoment B node1212 node1212Labels = _
    exact sound1212 B hB hF
  have h2479 : mixedVector B (Sum.inr 2479) = Sparse.eval nodeValue2479 (mixedVector B) := by
    change mixedMoment B node2479 node2479Labels = _
    exact sound2479 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1628, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1111, h1113, h1126, h1212, h2479, h4092, reducedSource1389] using sourceEq1628 B hB

theorem rowSound1389 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1389 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1389, numericCheck1389, reducedZero1389 B hB hF, mul_zero]

theorem reducedZero1390 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1390 (mixedVector B) = 0 := by
  have h623 : mixedVector B (Sum.inr 623) = Sparse.eval nodeValue623 (mixedVector B) := by
    change mixedMoment B node623 node623Labels = _
    exact sound623 B hB hF
  have h1126 : mixedVector B (Sum.inr 1126) = Sparse.eval nodeValue1126 (mixedVector B) := by
    change mixedMoment B node1126 node1126Labels = _
    exact sound1126 B hB hF
  have h1212 : mixedVector B (Sum.inr 1212) = Sparse.eval nodeValue1212 (mixedVector B) := by
    change mixedMoment B node1212 node1212Labels = _
    exact sound1212 B hB hF
  have h1233 : mixedVector B (Sum.inr 1233) = Sparse.eval nodeValue1233 (mixedVector B) := by
    change mixedMoment B node1233 node1233Labels = _
    exact sound1233 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1629, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h623, h1126, h1212, h1233, h1236, h4092, reducedSource1390] using sourceEq1629 B hB

theorem rowSound1390 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1390 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1390, numericCheck1390, reducedZero1390 B hB hF, mul_zero]

theorem reducedZero1391 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1391 (mixedVector B) = 0 := by
  have h629 : mixedVector B (Sum.inr 629) = Sparse.eval nodeValue629 (mixedVector B) := by
    change mixedMoment B node629 node629Labels = _
    exact sound629 B hB hF
  have h1135 : mixedVector B (Sum.inr 1135) = Sparse.eval nodeValue1135 (mixedVector B) := by
    change mixedMoment B node1135 node1135Labels = _
    exact sound1135 B hB hF
  have h1216 : mixedVector B (Sum.inr 1216) = Sparse.eval nodeValue1216 (mixedVector B) := by
    change mixedMoment B node1216 node1216Labels = _
    exact sound1216 B hB hF
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1630, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h629, h1135, h1216, h1235, h4091, reducedSource1391] using sourceEq1630 B hB

theorem rowSound1391 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1391 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1391, numericCheck1391, reducedZero1391 B hB hF, mul_zero]

theorem sourceRowsAt1376 : MixedData.sourceRows (1376 : Fin 2425) =
    MixedData.row1376 := by decide +kernel

theorem sourceRowsAt1377 : MixedData.sourceRows (1377 : Fin 2425) =
    MixedData.row1377 := by decide +kernel

theorem sourceRowsAt1378 : MixedData.sourceRows (1378 : Fin 2425) =
    MixedData.row1378 := by decide +kernel

theorem sourceRowsAt1379 : MixedData.sourceRows (1379 : Fin 2425) =
    MixedData.row1379 := by decide +kernel

theorem sourceRowsAt1380 : MixedData.sourceRows (1380 : Fin 2425) =
    MixedData.row1380 := by decide +kernel

theorem sourceRowsAt1381 : MixedData.sourceRows (1381 : Fin 2425) =
    MixedData.row1381 := by decide +kernel

theorem sourceRowsAt1382 : MixedData.sourceRows (1382 : Fin 2425) =
    MixedData.row1382 := by decide +kernel

theorem sourceRowsAt1383 : MixedData.sourceRows (1383 : Fin 2425) =
    MixedData.row1383 := by decide +kernel

theorem sourceRowsAt1384 : MixedData.sourceRows (1384 : Fin 2425) =
    MixedData.row1384 := by decide +kernel

theorem sourceRowsAt1385 : MixedData.sourceRows (1385 : Fin 2425) =
    MixedData.row1385 := by decide +kernel

theorem sourceRowsAt1386 : MixedData.sourceRows (1386 : Fin 2425) =
    MixedData.row1386 := by decide +kernel

theorem sourceRowsAt1387 : MixedData.sourceRows (1387 : Fin 2425) =
    MixedData.row1387 := by decide +kernel

theorem sourceRowsAt1388 : MixedData.sourceRows (1388 : Fin 2425) =
    MixedData.row1388 := by decide +kernel

theorem sourceRowsAt1389 : MixedData.sourceRows (1389 : Fin 2425) =
    MixedData.row1389 := by decide +kernel

theorem sourceRowsAt1390 : MixedData.sourceRows (1390 : Fin 2425) =
    MixedData.row1390 := by decide +kernel

theorem sourceRowsAt1391 : MixedData.sourceRows (1391 : Fin 2425) =
    MixedData.row1391 := by decide +kernel

theorem chunkSound86 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 86) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1376 ∨ k.val = 1377 ∨ k.val = 1378 ∨ k.val = 1379 ∨ k.val = 1380 ∨ k.val = 1381 ∨ k.val = 1382 ∨ k.val = 1383 ∨ k.val = 1384 ∨ k.val = 1385 ∨ k.val = 1386 ∨ k.val = 1387 ∨ k.val = 1388 ∨ k.val = 1389 ∨ k.val = 1390 ∨ k.val = 1391 := by omega
  rcases heq with h1376 | h1377 | h1378 | h1379 | h1380 | h1381 | h1382 | h1383 | h1384 | h1385 | h1386 | h1387 | h1388 | h1389 | h1390 | h1391
  · have he : k = (1376 : Fin 2425) := Fin.ext h1376
    subst k
    rw [sourceRowsAt1376]
    exact rowSound1376 B hB hF
  · have he : k = (1377 : Fin 2425) := Fin.ext h1377
    subst k
    rw [sourceRowsAt1377]
    exact rowSound1377 B hB hF
  · have he : k = (1378 : Fin 2425) := Fin.ext h1378
    subst k
    rw [sourceRowsAt1378]
    exact rowSound1378 B hB hF
  · have he : k = (1379 : Fin 2425) := Fin.ext h1379
    subst k
    rw [sourceRowsAt1379]
    exact rowSound1379 B hB hF
  · have he : k = (1380 : Fin 2425) := Fin.ext h1380
    subst k
    rw [sourceRowsAt1380]
    exact rowSound1380 B hB hF
  · have he : k = (1381 : Fin 2425) := Fin.ext h1381
    subst k
    rw [sourceRowsAt1381]
    exact rowSound1381 B hB hF
  · have he : k = (1382 : Fin 2425) := Fin.ext h1382
    subst k
    rw [sourceRowsAt1382]
    exact rowSound1382 B hB hF
  · have he : k = (1383 : Fin 2425) := Fin.ext h1383
    subst k
    rw [sourceRowsAt1383]
    exact rowSound1383 B hB hF
  · have he : k = (1384 : Fin 2425) := Fin.ext h1384
    subst k
    rw [sourceRowsAt1384]
    exact rowSound1384 B hB hF
  · have he : k = (1385 : Fin 2425) := Fin.ext h1385
    subst k
    rw [sourceRowsAt1385]
    exact rowSound1385 B hB hF
  · have he : k = (1386 : Fin 2425) := Fin.ext h1386
    subst k
    rw [sourceRowsAt1386]
    exact rowSound1386 B hB hF
  · have he : k = (1387 : Fin 2425) := Fin.ext h1387
    subst k
    rw [sourceRowsAt1387]
    exact rowSound1387 B hB hF
  · have he : k = (1388 : Fin 2425) := Fin.ext h1388
    subst k
    rw [sourceRowsAt1388]
    exact rowSound1388 B hB hF
  · have he : k = (1389 : Fin 2425) := Fin.ext h1389
    subst k
    rw [sourceRowsAt1389]
    exact rowSound1389 B hB hF
  · have he : k = (1390 : Fin 2425) := Fin.ext h1390
    subst k
    rw [sourceRowsAt1390]
    exact rowSound1390 B hB hF
  · have he : k = (1391 : Fin 2425) := Fin.ext h1391
    subst k
    rw [sourceRowsAt1391]
    exact rowSound1391 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
