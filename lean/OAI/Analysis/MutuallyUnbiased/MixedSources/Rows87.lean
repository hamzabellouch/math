import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic87
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources51

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1392 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1392 (mixedVector B) = 0 := by
  have h1116 : mixedVector B (Sum.inr 1116) = Sparse.eval nodeValue1116 (mixedVector B) := by
    change mixedMoment B node1116 node1116Labels = _
    exact sound1116 B hB hF
  have h1117 : mixedVector B (Sum.inr 1117) = Sparse.eval nodeValue1117 (mixedVector B) := by
    change mixedMoment B node1117 node1117Labels = _
    exact sound1117 B hB hF
  have h1135 : mixedVector B (Sum.inr 1135) = Sparse.eval nodeValue1135 (mixedVector B) := by
    change mixedMoment B node1135 node1135Labels = _
    exact sound1135 B hB hF
  have h1216 : mixedVector B (Sum.inr 1216) = Sparse.eval nodeValue1216 (mixedVector B) := by
    change mixedMoment B node1216 node1216Labels = _
    exact sound1216 B hB hF
  have h2483 : mixedVector B (Sum.inr 2483) = Sparse.eval nodeValue2483 (mixedVector B) := by
    change mixedMoment B node2483 node2483Labels = _
    exact sound2483 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1631, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1116, h1117, h1135, h1216, h2483, h4091, reducedSource1392] using sourceEq1631 B hB

theorem rowSound1392 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1392 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1392, numericCheck1392, reducedZero1392 B hB hF, mul_zero]

theorem reducedZero1393 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1393 (mixedVector B) = 0 := by
  have h1607 : mixedVector B (Sum.inr 1607) = Sparse.eval nodeValue1607 (mixedVector B) := by
    change mixedMoment B node1607 node1607Labels = _
    exact sound1607 B hB hF
  have h1609 : mixedVector B (Sum.inr 1609) = Sparse.eval nodeValue1609 (mixedVector B) := by
    change mixedMoment B node1609 node1609Labels = _
    exact sound1609 B hB hF
  have h1616 : mixedVector B (Sum.inr 1616) = Sparse.eval nodeValue1616 (mixedVector B) := by
    change mixedMoment B node1616 node1616Labels = _
    exact sound1616 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1632, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1607, h1609, h1616, h1737, h3288, h4069, reducedSource1393] using sourceEq1632 B hB

theorem rowSound1393 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1393 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1393, numericCheck1393, reducedZero1393 B hB hF, mul_zero]

theorem reducedZero1394 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1394 (mixedVector B) = 0 := by
  have h1592 : mixedVector B (Sum.inr 1592) = Sparse.eval nodeValue1592 (mixedVector B) := by
    change mixedMoment B node1592 node1592Labels = _
    exact sound1592 B hB hF
  have h1594 : mixedVector B (Sum.inr 1594) = Sparse.eval nodeValue1594 (mixedVector B) := by
    change mixedMoment B node1594 node1594Labels = _
    exact sound1594 B hB hF
  have h1597 : mixedVector B (Sum.inr 1597) = Sparse.eval nodeValue1597 (mixedVector B) := by
    change mixedMoment B node1597 node1597Labels = _
    exact sound1597 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1633, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1592, h1594, h1597, h1707, h3288, h4069, reducedSource1394] using sourceEq1633 B hB

theorem rowSound1394 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1394 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1394, numericCheck1394, reducedZero1394 B hB hF, mul_zero]

theorem reducedZero1395 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1395 (mixedVector B) = 0 := by
  have h1597 : mixedVector B (Sum.inr 1597) = Sparse.eval nodeValue1597 (mixedVector B) := by
    change mixedMoment B node1597 node1597Labels = _
    exact sound1597 B hB hF
  have h3238 : mixedVector B (Sum.inr 3238) = Sparse.eval nodeValue3238 (mixedVector B) := by
    change mixedMoment B node3238 node3238Labels = _
    exact sound3238 B hB hF
  have h3285 : mixedVector B (Sum.inr 3285) = Sparse.eval nodeValue3285 (mixedVector B) := by
    change mixedMoment B node3285 node3285Labels = _
    exact sound3285 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1634, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1597, h3238, h3285, h3288, h3290, h3293, h4069, reducedSource1395] using sourceEq1634 B hB

theorem rowSound1395 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1395 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1395, numericCheck1395, reducedZero1395 B hB hF, mul_zero]

theorem reducedZero1396 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1396 (mixedVector B) = 0 := by
  have h1616 : mixedVector B (Sum.inr 1616) = Sparse.eval nodeValue1616 (mixedVector B) := by
    change mixedMoment B node1616 node1616Labels = _
    exact sound1616 B hB hF
  have h3241 : mixedVector B (Sum.inr 3241) = Sparse.eval nodeValue3241 (mixedVector B) := by
    change mixedMoment B node3241 node3241Labels = _
    exact sound3241 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1635, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1616, h3241, h3288, h3290, h3299, h4069, reducedSource1396] using sourceEq1635 B hB

theorem rowSound1396 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1396 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1396, numericCheck1396, reducedZero1396 B hB hF, mul_zero]

theorem reducedZero1397 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1397 (mixedVector B) = 0 := by
  have h1112 : mixedVector B (Sum.inr 1112) = Sparse.eval nodeValue1112 (mixedVector B) := by
    change mixedMoment B node1112 node1112Labels = _
    exact sound1112 B hB hF
  have h1114 : mixedVector B (Sum.inr 1114) = Sparse.eval nodeValue1114 (mixedVector B) := by
    change mixedMoment B node1114 node1114Labels = _
    exact sound1114 B hB hF
  have h1117 : mixedVector B (Sum.inr 1117) = Sparse.eval nodeValue1117 (mixedVector B) := by
    change mixedMoment B node1117 node1117Labels = _
    exact sound1117 B hB hF
  have h1129 : mixedVector B (Sum.inr 1129) = Sparse.eval nodeValue1129 (mixedVector B) := by
    change mixedMoment B node1129 node1129Labels = _
    exact sound1129 B hB hF
  have h1213 : mixedVector B (Sum.inr 1213) = Sparse.eval nodeValue1213 (mixedVector B) := by
    change mixedMoment B node1213 node1213Labels = _
    exact sound1213 B hB hF
  have h2480 : mixedVector B (Sum.inr 2480) = Sparse.eval nodeValue2480 (mixedVector B) := by
    change mixedMoment B node2480 node2480Labels = _
    exact sound2480 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1636, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1112, h1114, h1117, h1129, h1213, h2480, h4091, reducedSource1397] using sourceEq1636 B hB

theorem rowSound1397 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1397 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1397, numericCheck1397, reducedZero1397 B hB hF, mul_zero]

theorem reducedZero1398 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1398 (mixedVector B) = 0 := by
  have h625 : mixedVector B (Sum.inr 625) = Sparse.eval nodeValue625 (mixedVector B) := by
    change mixedMoment B node625 node625Labels = _
    exact sound625 B hB hF
  have h1129 : mixedVector B (Sum.inr 1129) = Sparse.eval nodeValue1129 (mixedVector B) := by
    change mixedMoment B node1129 node1129Labels = _
    exact sound1129 B hB hF
  have h1213 : mixedVector B (Sum.inr 1213) = Sparse.eval nodeValue1213 (mixedVector B) := by
    change mixedMoment B node1213 node1213Labels = _
    exact sound1213 B hB hF
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1637, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h625, h1129, h1213, h1235, h1240, h4091, reducedSource1398] using sourceEq1637 B hB

theorem rowSound1398 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1398 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1398, numericCheck1398, reducedZero1398 B hB hF, mul_zero]

theorem reducedZero1399 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1399 (mixedVector B) = 0 := by
  have h1597 : mixedVector B (Sum.inr 1597) = Sparse.eval nodeValue1597 (mixedVector B) := by
    change mixedMoment B node1597 node1597Labels = _
    exact sound1597 B hB hF
  have h1598 : mixedVector B (Sum.inr 1598) = Sparse.eval nodeValue1598 (mixedVector B) := by
    change mixedMoment B node1598 node1598Labels = _
    exact sound1598 B hB hF
  have h1601 : mixedVector B (Sum.inr 1601) = Sparse.eval nodeValue1601 (mixedVector B) := by
    change mixedMoment B node1601 node1601Labels = _
    exact sound1601 B hB hF
  have h1616 : mixedVector B (Sum.inr 1616) = Sparse.eval nodeValue1616 (mixedVector B) := by
    change mixedMoment B node1616 node1616Labels = _
    exact sound1616 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1638, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1597, h1598, h1601, h1616, h1724, h3290, h4069, reducedSource1399] using sourceEq1638 B hB

theorem rowSound1399 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1399 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1399, numericCheck1399, reducedZero1399 B hB hF, mul_zero]

theorem reducedZero1400 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1400 (mixedVector B) = 0 := by
  have h1210 : mixedVector B (Sum.inr 1210) = Sparse.eval nodeValue1210 (mixedVector B) := by
    change mixedMoment B node1210 node1210Labels = _
    exact sound1210 B hB hF
  have h2477 : mixedVector B (Sum.inr 2477) = Sparse.eval nodeValue2477 (mixedVector B) := by
    change mixedMoment B node2477 node2477Labels = _
    exact sound2477 B hB hF
  have h2613 : mixedVector B (Sum.inr 2613) = Sparse.eval nodeValue2613 (mixedVector B) := by
    change mixedMoment B node2613 node2613Labels = _
    exact sound2613 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h2708 : mixedVector B (Sum.inr 2708) = Sparse.eval nodeValue2708 (mixedVector B) := by
    change mixedMoment B node2708 node2708Labels = _
    exact sound2708 B hB hF
  have h2718 : mixedVector B (Sum.inr 2718) = Sparse.eval nodeValue2718 (mixedVector B) := by
    change mixedMoment B node2718 node2718Labels = _
    exact sound2718 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1639, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1210, h2477, h2613, h2694, h2708, h2718, h4090, reducedSource1400] using sourceEq1639 B hB

theorem rowSound1400 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1400 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1400, numericCheck1400, reducedZero1400 B hB hF, mul_zero]

theorem reducedZero1401 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1401 (mixedVector B) = 0 := by
  have h1180 : mixedVector B (Sum.inr 1180) = Sparse.eval nodeValue1180 (mixedVector B) := by
    change mixedMoment B node1180 node1180Labels = _
    exact sound1180 B hB hF
  have h2383 : mixedVector B (Sum.inr 2383) = Sparse.eval nodeValue2383 (mixedVector B) := by
    change mixedMoment B node2383 node2383Labels = _
    exact sound2383 B hB hF
  have h2607 : mixedVector B (Sum.inr 2607) = Sparse.eval nodeValue2607 (mixedVector B) := by
    change mixedMoment B node2607 node2607Labels = _
    exact sound2607 B hB hF
  have h2662 : mixedVector B (Sum.inr 2662) = Sparse.eval nodeValue2662 (mixedVector B) := by
    change mixedMoment B node2662 node2662Labels = _
    exact sound2662 B hB hF
  have h2671 : mixedVector B (Sum.inr 2671) = Sparse.eval nodeValue2671 (mixedVector B) := by
    change mixedMoment B node2671 node2671Labels = _
    exact sound2671 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  simpa only [sourceForm1640, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1180, h2383, h2607, h2662, h2671, h4087, reducedSource1401] using sourceEq1640 B hB

theorem rowSound1401 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1401 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1401, numericCheck1401, reducedZero1401 B hB hF, mul_zero]

theorem reducedZero1402 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1402 (mixedVector B) = 0 := by
  have h1180 : mixedVector B (Sum.inr 1180) = Sparse.eval nodeValue1180 (mixedVector B) := by
    change mixedMoment B node1180 node1180Labels = _
    exact sound1180 B hB hF
  have h1187 : mixedVector B (Sum.inr 1187) = Sparse.eval nodeValue1187 (mixedVector B) := by
    change mixedMoment B node1187 node1187Labels = _
    exact sound1187 B hB hF
  have h1256 : mixedVector B (Sum.inr 1256) = Sparse.eval nodeValue1256 (mixedVector B) := by
    change mixedMoment B node1256 node1256Labels = _
    exact sound1256 B hB hF
  have h2671 : mixedVector B (Sum.inr 2671) = Sparse.eval nodeValue2671 (mixedVector B) := by
    change mixedMoment B node2671 node2671Labels = _
    exact sound2671 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  simpa only [sourceForm1641, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1180, h1187, h1256, h2671, h4087, reducedSource1402] using sourceEq1641 B hB

theorem rowSound1402 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1402 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1402, numericCheck1402, reducedZero1402 B hB hF, mul_zero]

theorem reducedZero1403 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1403 (mixedVector B) = 0 := by
  have h1178 : mixedVector B (Sum.inr 1178) = Sparse.eval nodeValue1178 (mixedVector B) := by
    change mixedMoment B node1178 node1178Labels = _
    exact sound1178 B hB hF
  have h2382 : mixedVector B (Sum.inr 2382) = Sparse.eval nodeValue2382 (mixedVector B) := by
    change mixedMoment B node2382 node2382Labels = _
    exact sound2382 B hB hF
  have h2606 : mixedVector B (Sum.inr 2606) = Sparse.eval nodeValue2606 (mixedVector B) := by
    change mixedMoment B node2606 node2606Labels = _
    exact sound2606 B hB hF
  have h2661 : mixedVector B (Sum.inr 2661) = Sparse.eval nodeValue2661 (mixedVector B) := by
    change mixedMoment B node2661 node2661Labels = _
    exact sound2661 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1642, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1178, h2382, h2606, h2661, h2669, h2672, h4088, reducedSource1403] using sourceEq1642 B hB

theorem rowSound1403 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1403 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1403, numericCheck1403, reducedZero1403 B hB hF, mul_zero]

theorem reducedZero1404 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1404 (mixedVector B) = 0 := by
  have h1656 : mixedVector B (Sum.inr 1656) = Sparse.eval nodeValue1656 (mixedVector B) := by
    change mixedMoment B node1656 node1656Labels = _
    exact sound1656 B hB hF
  have h1659 : mixedVector B (Sum.inr 1659) = Sparse.eval nodeValue1659 (mixedVector B) := by
    change mixedMoment B node1659 node1659Labels = _
    exact sound1659 B hB hF
  have h1661 : mixedVector B (Sum.inr 1661) = Sparse.eval nodeValue1661 (mixedVector B) := by
    change mixedMoment B node1661 node1661Labels = _
    exact sound1661 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1643, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1656, h1659, h1661, h1739, h2737, h4069, reducedSource1404] using sourceEq1643 B hB

theorem rowSound1404 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1404 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1404, numericCheck1404, reducedZero1404 B hB hF, mul_zero]

theorem reducedZero1405 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1405 (mixedVector B) = 0 := by
  have h1650 : mixedVector B (Sum.inr 1650) = Sparse.eval nodeValue1650 (mixedVector B) := by
    change mixedMoment B node1650 node1650Labels = _
    exact sound1650 B hB hF
  have h2502 : mixedVector B (Sum.inr 2502) = Sparse.eval nodeValue2502 (mixedVector B) := by
    change mixedMoment B node2502 node2502Labels = _
    exact sound2502 B hB hF
  have h2521 : mixedVector B (Sum.inr 2521) = Sparse.eval nodeValue2521 (mixedVector B) := by
    change mixedMoment B node2521 node2521Labels = _
    exact sound2521 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1644, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1650, h2502, h2521, h2737, h3305, h4069, reducedSource1405] using sourceEq1644 B hB

theorem rowSound1405 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1405 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1405, numericCheck1405, reducedZero1405 B hB hF, mul_zero]

theorem reducedZero1406 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1406 (mixedVector B) = 0 := by
  have h1646 : mixedVector B (Sum.inr 1646) = Sparse.eval nodeValue1646 (mixedVector B) := by
    change mixedMoment B node1646 node1646Labels = _
    exact sound1646 B hB hF
  have h1651 : mixedVector B (Sum.inr 1651) = Sparse.eval nodeValue1651 (mixedVector B) := by
    change mixedMoment B node1651 node1651Labels = _
    exact sound1651 B hB hF
  have h1653 : mixedVector B (Sum.inr 1653) = Sparse.eval nodeValue1653 (mixedVector B) := by
    change mixedMoment B node1653 node1653Labels = _
    exact sound1653 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h3306 : mixedVector B (Sum.inr 3306) = Sparse.eval nodeValue3306 (mixedVector B) := by
    change mixedMoment B node3306 node3306Labels = _
    exact sound3306 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1645, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1646, h1651, h1653, h1728, h3306, h4069, reducedSource1406] using sourceEq1645 B hB

theorem rowSound1406 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1406 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1406, numericCheck1406, reducedZero1406 B hB hF, mul_zero]

theorem reducedZero1407 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1407 (mixedVector B) = 0 := by
  have h1653 : mixedVector B (Sum.inr 1653) = Sparse.eval nodeValue1653 (mixedVector B) := by
    change mixedMoment B node1653 node1653Labels = _
    exact sound1653 B hB hF
  have h3049 : mixedVector B (Sum.inr 3049) = Sparse.eval nodeValue3049 (mixedVector B) := by
    change mixedMoment B node3049 node3049Labels = _
    exact sound3049 B hB hF
  have h3287 : mixedVector B (Sum.inr 3287) = Sparse.eval nodeValue3287 (mixedVector B) := by
    change mixedMoment B node3287 node3287Labels = _
    exact sound3287 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3306 : mixedVector B (Sum.inr 3306) = Sparse.eval nodeValue3306 (mixedVector B) := by
    change mixedMoment B node3306 node3306Labels = _
    exact sound3306 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1646, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1653, h3049, h3287, h3305, h3306, h4069, reducedSource1407] using sourceEq1646 B hB

theorem rowSound1407 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1407 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1407, numericCheck1407, reducedZero1407 B hB hF, mul_zero]

theorem sourceRowsAt1392 : MixedData.sourceRows (1392 : Fin 2425) =
    MixedData.row1392 := by decide +kernel

theorem sourceRowsAt1393 : MixedData.sourceRows (1393 : Fin 2425) =
    MixedData.row1393 := by decide +kernel

theorem sourceRowsAt1394 : MixedData.sourceRows (1394 : Fin 2425) =
    MixedData.row1394 := by decide +kernel

theorem sourceRowsAt1395 : MixedData.sourceRows (1395 : Fin 2425) =
    MixedData.row1395 := by decide +kernel

theorem sourceRowsAt1396 : MixedData.sourceRows (1396 : Fin 2425) =
    MixedData.row1396 := by decide +kernel

theorem sourceRowsAt1397 : MixedData.sourceRows (1397 : Fin 2425) =
    MixedData.row1397 := by decide +kernel

theorem sourceRowsAt1398 : MixedData.sourceRows (1398 : Fin 2425) =
    MixedData.row1398 := by decide +kernel

theorem sourceRowsAt1399 : MixedData.sourceRows (1399 : Fin 2425) =
    MixedData.row1399 := by decide +kernel

theorem sourceRowsAt1400 : MixedData.sourceRows (1400 : Fin 2425) =
    MixedData.row1400 := by decide +kernel

theorem sourceRowsAt1401 : MixedData.sourceRows (1401 : Fin 2425) =
    MixedData.row1401 := by decide +kernel

theorem sourceRowsAt1402 : MixedData.sourceRows (1402 : Fin 2425) =
    MixedData.row1402 := by decide +kernel

theorem sourceRowsAt1403 : MixedData.sourceRows (1403 : Fin 2425) =
    MixedData.row1403 := by decide +kernel

theorem sourceRowsAt1404 : MixedData.sourceRows (1404 : Fin 2425) =
    MixedData.row1404 := by decide +kernel

theorem sourceRowsAt1405 : MixedData.sourceRows (1405 : Fin 2425) =
    MixedData.row1405 := by decide +kernel

theorem sourceRowsAt1406 : MixedData.sourceRows (1406 : Fin 2425) =
    MixedData.row1406 := by decide +kernel

theorem sourceRowsAt1407 : MixedData.sourceRows (1407 : Fin 2425) =
    MixedData.row1407 := by decide +kernel

theorem chunkSound87 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 87) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1392 ∨ k.val = 1393 ∨ k.val = 1394 ∨ k.val = 1395 ∨ k.val = 1396 ∨ k.val = 1397 ∨ k.val = 1398 ∨ k.val = 1399 ∨ k.val = 1400 ∨ k.val = 1401 ∨ k.val = 1402 ∨ k.val = 1403 ∨ k.val = 1404 ∨ k.val = 1405 ∨ k.val = 1406 ∨ k.val = 1407 := by omega
  rcases heq with h1392 | h1393 | h1394 | h1395 | h1396 | h1397 | h1398 | h1399 | h1400 | h1401 | h1402 | h1403 | h1404 | h1405 | h1406 | h1407
  · have he : k = (1392 : Fin 2425) := Fin.ext h1392
    subst k
    rw [sourceRowsAt1392]
    exact rowSound1392 B hB hF
  · have he : k = (1393 : Fin 2425) := Fin.ext h1393
    subst k
    rw [sourceRowsAt1393]
    exact rowSound1393 B hB hF
  · have he : k = (1394 : Fin 2425) := Fin.ext h1394
    subst k
    rw [sourceRowsAt1394]
    exact rowSound1394 B hB hF
  · have he : k = (1395 : Fin 2425) := Fin.ext h1395
    subst k
    rw [sourceRowsAt1395]
    exact rowSound1395 B hB hF
  · have he : k = (1396 : Fin 2425) := Fin.ext h1396
    subst k
    rw [sourceRowsAt1396]
    exact rowSound1396 B hB hF
  · have he : k = (1397 : Fin 2425) := Fin.ext h1397
    subst k
    rw [sourceRowsAt1397]
    exact rowSound1397 B hB hF
  · have he : k = (1398 : Fin 2425) := Fin.ext h1398
    subst k
    rw [sourceRowsAt1398]
    exact rowSound1398 B hB hF
  · have he : k = (1399 : Fin 2425) := Fin.ext h1399
    subst k
    rw [sourceRowsAt1399]
    exact rowSound1399 B hB hF
  · have he : k = (1400 : Fin 2425) := Fin.ext h1400
    subst k
    rw [sourceRowsAt1400]
    exact rowSound1400 B hB hF
  · have he : k = (1401 : Fin 2425) := Fin.ext h1401
    subst k
    rw [sourceRowsAt1401]
    exact rowSound1401 B hB hF
  · have he : k = (1402 : Fin 2425) := Fin.ext h1402
    subst k
    rw [sourceRowsAt1402]
    exact rowSound1402 B hB hF
  · have he : k = (1403 : Fin 2425) := Fin.ext h1403
    subst k
    rw [sourceRowsAt1403]
    exact rowSound1403 B hB hF
  · have he : k = (1404 : Fin 2425) := Fin.ext h1404
    subst k
    rw [sourceRowsAt1404]
    exact rowSound1404 B hB hF
  · have he : k = (1405 : Fin 2425) := Fin.ext h1405
    subst k
    rw [sourceRowsAt1405]
    exact rowSound1405 B hB hF
  · have he : k = (1406 : Fin 2425) := Fin.ext h1406
    subst k
    rw [sourceRowsAt1406]
    exact rowSound1406 B hB hF
  · have he : k = (1407 : Fin 2425) := Fin.ext h1407
    subst k
    rw [sourceRowsAt1407]
    exact rowSound1407 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
