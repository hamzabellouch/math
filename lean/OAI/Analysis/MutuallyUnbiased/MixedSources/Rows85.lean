import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources50

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1360 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1360 (mixedVector B) = 0 := by
  have h782 : mixedVector B (Sum.inr 782) = Sparse.eval nodeValue782 (mixedVector B) := by
    change mixedMoment B node782 node782Labels = _
    exact sound782 B hB hF
  have h784 : mixedVector B (Sum.inr 784) = Sparse.eval nodeValue784 (mixedVector B) := by
    change mixedMoment B node784 node784Labels = _
    exact sound784 B hB hF
  have h803 : mixedVector B (Sum.inr 803) = Sparse.eval nodeValue803 (mixedVector B) := by
    change mixedMoment B node803 node803Labels = _
    exact sound803 B hB hF
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1596, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h782, h784, h803, h1705, h4069, reducedSource1360] using sourceEq1596 B hB

theorem rowSound1360 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1360 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1360, numericCheck1360, reducedZero1360 B hB hF, mul_zero]

theorem reducedZero1361 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1361 (mixedVector B) = 0 := by
  have h803 : mixedVector B (Sum.inr 803) = Sparse.eval nodeValue803 (mixedVector B) := by
    change mixedMoment B node803 node803Labels = _
    exact sound803 B hB hF
  have h1642 : mixedVector B (Sum.inr 1642) = Sparse.eval nodeValue1642 (mixedVector B) := by
    change mixedMoment B node1642 node1642Labels = _
    exact sound1642 B hB hF
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1597, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h803, h1642, h1705, h1713, h1724, h4069, reducedSource1361] using sourceEq1597 B hB

theorem rowSound1361 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1361 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1361, numericCheck1361, reducedZero1361 B hB hF, mul_zero]

theorem reducedZero1362 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1362 (mixedVector B) = 0 := by
  have h782 : mixedVector B (Sum.inr 782) = Sparse.eval nodeValue782 (mixedVector B) := by
    change mixedMoment B node782 node782Labels = _
    exact sound782 B hB hF
  have h1635 : mixedVector B (Sum.inr 1635) = Sparse.eval nodeValue1635 (mixedVector B) := by
    change mixedMoment B node1635 node1635Labels = _
    exact sound1635 B hB hF
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1598, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h782, h1635, h1705, h1707, h4069, reducedSource1362] using sourceEq1598 B hB

theorem rowSound1362 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1362 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1362, numericCheck1362, reducedZero1362 B hB hF, mul_zero]

theorem reducedZero1363 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1363 (mixedVector B) = 0 := by
  have h580 : mixedVector B (Sum.inr 580) = Sparse.eval nodeValue580 (mixedVector B) := by
    change mixedMoment B node580 node580Labels = _
    exact sound580 B hB hF
  have h944 : mixedVector B (Sum.inr 944) = Sparse.eval nodeValue944 (mixedVector B) := by
    change mixedMoment B node944 node944Labels = _
    exact sound944 B hB hF
  have h1021 : mixedVector B (Sum.inr 1021) = Sparse.eval nodeValue1021 (mixedVector B) := by
    change mixedMoment B node1021 node1021Labels = _
    exact sound1021 B hB hF
  have h1039 : mixedVector B (Sum.inr 1039) = Sparse.eval nodeValue1039 (mixedVector B) := by
    change mixedMoment B node1039 node1039Labels = _
    exact sound1039 B hB hF
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1600, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h580, h944, h1021, h1039, h1044, h4083, reducedSource1363] using sourceEq1600 B hB

theorem rowSound1363 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1363 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1363, numericCheck1363, reducedZero1363 B hB hF, mul_zero]

theorem reducedZero1364 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1364 (mixedVector B) = 0 := by
  have h1327 : mixedVector B (Sum.inr 1327) = Sparse.eval nodeValue1327 (mixedVector B) := by
    change mixedMoment B node1327 node1327Labels = _
    exact sound1327 B hB hF
  have h1328 : mixedVector B (Sum.inr 1328) = Sparse.eval nodeValue1328 (mixedVector B) := by
    change mixedMoment B node1328 node1328Labels = _
    exact sound1328 B hB hF
  have h1330 : mixedVector B (Sum.inr 1330) = Sparse.eval nodeValue1330 (mixedVector B) := by
    change mixedMoment B node1330 node1330Labels = _
    exact sound1330 B hB hF
  have h1335 : mixedVector B (Sum.inr 1335) = Sparse.eval nodeValue1335 (mixedVector B) := by
    change mixedMoment B node1335 node1335Labels = _
    exact sound1335 B hB hF
  have h1383 : mixedVector B (Sum.inr 1383) = Sparse.eval nodeValue1383 (mixedVector B) := by
    change mixedMoment B node1383 node1383Labels = _
    exact sound1383 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1601, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1327, h1328, h1330, h1335, h1383, h2924, h4091, reducedSource1364] using sourceEq1601 B hB

theorem rowSound1364 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1364 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1364, numericCheck1364, reducedZero1364 B hB hF, mul_zero]

theorem reducedZero1365 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1365 (mixedVector B) = 0 := by
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h2457 : mixedVector B (Sum.inr 2457) = Sparse.eval nodeValue2457 (mixedVector B) := by
    change mixedMoment B node2457 node2457Labels = _
    exact sound2457 B hB hF
  have h3278 : mixedVector B (Sum.inr 3278) = Sparse.eval nodeValue3278 (mixedVector B) := by
    change mixedMoment B node3278 node3278Labels = _
    exact sound3278 B hB hF
  have h3281 : mixedVector B (Sum.inr 3281) = Sparse.eval nodeValue3281 (mixedVector B) := by
    change mixedMoment B node3281 node3281Labels = _
    exact sound3281 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1602, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1713, h2457, h3278, h3281, h3293, h4069, reducedSource1365] using sourceEq1602 B hB

theorem rowSound1365 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1365 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1365, numericCheck1365, reducedZero1365 B hB hF, mul_zero]

theorem reducedZero1366 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1366 (mixedVector B) = 0 := by
  have h822 : mixedVector B (Sum.inr 822) = Sparse.eval nodeValue822 (mixedVector B) := by
    change mixedMoment B node822 node822Labels = _
    exact sound822 B hB hF
  have h1654 : mixedVector B (Sum.inr 1654) = Sparse.eval nodeValue1654 (mixedVector B) := by
    change mixedMoment B node1654 node1654Labels = _
    exact sound1654 B hB hF
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1604, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h822, h1654, h1713, h1737, h4069, reducedSource1366] using sourceEq1604 B hB

theorem rowSound1366 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1366 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1366, numericCheck1366, reducedZero1366 B hB hF, mul_zero]

theorem reducedZero1367 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1367 (mixedVector B) = 0 := by
  have h1125 : mixedVector B (Sum.inr 1125) = Sparse.eval nodeValue1125 (mixedVector B) := by
    change mixedMoment B node1125 node1125Labels = _
    exact sound1125 B hB hF
  have h1128 : mixedVector B (Sum.inr 1128) = Sparse.eval nodeValue1128 (mixedVector B) := by
    change mixedMoment B node1128 node1128Labels = _
    exact sound1128 B hB hF
  have h1133 : mixedVector B (Sum.inr 1133) = Sparse.eval nodeValue1133 (mixedVector B) := by
    change mixedMoment B node1133 node1133Labels = _
    exact sound1133 B hB hF
  have h1234 : mixedVector B (Sum.inr 1234) = Sparse.eval nodeValue1234 (mixedVector B) := by
    change mixedMoment B node1234 node1234Labels = _
    exact sound1234 B hB hF
  have h2509 : mixedVector B (Sum.inr 2509) = Sparse.eval nodeValue2509 (mixedVector B) := by
    change mixedMoment B node2509 node2509Labels = _
    exact sound2509 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1606, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1125, h1128, h1133, h1234, h2509, h4084, reducedSource1367] using sourceEq1606 B hB

theorem rowSound1367 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1367 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1367, numericCheck1367, reducedZero1367 B hB hF, mul_zero]

theorem reducedZero1368 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1368 (mixedVector B) = 0 := by
  have h651 : mixedVector B (Sum.inr 651) = Sparse.eval nodeValue651 (mixedVector B) := by
    change mixedMoment B node651 node651Labels = _
    exact sound651 B hB hF
  have h1169 : mixedVector B (Sum.inr 1169) = Sparse.eval nodeValue1169 (mixedVector B) := by
    change mixedMoment B node1169 node1169Labels = _
    exact sound1169 B hB hF
  have h1270 : mixedVector B (Sum.inr 1270) = Sparse.eval nodeValue1270 (mixedVector B) := by
    change mixedMoment B node1270 node1270Labels = _
    exact sound1270 B hB hF
  have h1293 : mixedVector B (Sum.inr 1293) = Sparse.eval nodeValue1293 (mixedVector B) := by
    change mixedMoment B node1293 node1293Labels = _
    exact sound1293 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1607, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h651, h1169, h1270, h1293, h4091, reducedSource1368] using sourceEq1607 B hB

theorem rowSound1368 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1368 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1368, numericCheck1368, reducedZero1368 B hB hF, mul_zero]

theorem reducedZero1369 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1369 (mixedVector B) = 0 := by
  have h1654 : mixedVector B (Sum.inr 1654) = Sparse.eval nodeValue1654 (mixedVector B) := by
    change mixedMoment B node1654 node1654Labels = _
    exact sound1654 B hB hF
  have h1656 : mixedVector B (Sum.inr 1656) = Sparse.eval nodeValue1656 (mixedVector B) := by
    change mixedMoment B node1656 node1656Labels = _
    exact sound1656 B hB hF
  have h1658 : mixedVector B (Sum.inr 1658) = Sparse.eval nodeValue1658 (mixedVector B) := by
    change mixedMoment B node1658 node1658Labels = _
    exact sound1658 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1608, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1654, h1656, h1658, h1737, h2702, h4069, reducedSource1369] using sourceEq1608 B hB

theorem rowSound1369 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1369 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1369, numericCheck1369, reducedZero1369 B hB hF, mul_zero]

theorem reducedZero1370 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1370 (mixedVector B) = 0 := by
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h3308 : mixedVector B (Sum.inr 3308) = Sparse.eval nodeValue3308 (mixedVector B) := by
    change mixedMoment B node3308 node3308Labels = _
    exact sound3308 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1609, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1710, h2702, h2737, h3308, h4069, reducedSource1370] using sourceEq1609 B hB

theorem rowSound1370 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1370 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1370, numericCheck1370, reducedZero1370 B hB hF, mul_zero]

theorem reducedZero1371 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1371 (mixedVector B) = 0 := by
  have h1602 : mixedVector B (Sum.inr 1602) = Sparse.eval nodeValue1602 (mixedVector B) := by
    change mixedMoment B node1602 node1602Labels = _
    exact sound1602 B hB hF
  have h2457 : mixedVector B (Sum.inr 2457) = Sparse.eval nodeValue2457 (mixedVector B) := by
    change mixedMoment B node2457 node2457Labels = _
    exact sound2457 B hB hF
  have h2466 : mixedVector B (Sum.inr 2466) = Sparse.eval nodeValue2466 (mixedVector B) := by
    change mixedMoment B node2466 node2466Labels = _
    exact sound2466 B hB hF
  have h2502 : mixedVector B (Sum.inr 2502) = Sparse.eval nodeValue2502 (mixedVector B) := by
    change mixedMoment B node2502 node2502Labels = _
    exact sound2502 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1610, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1602, h2457, h2466, h2502, h2702, h3293, h4069, reducedSource1371] using sourceEq1610 B hB

theorem rowSound1371 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1371 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1371, numericCheck1371, reducedZero1371 B hB hF, mul_zero]

theorem reducedZero1372 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1372 (mixedVector B) = 0 := by
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3308 : mixedVector B (Sum.inr 3308) = Sparse.eval nodeValue3308 (mixedVector B) := by
    change mixedMoment B node3308 node3308Labels = _
    exact sound3308 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1611, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1737, h2702, h3288, h3293, h3308, h4069, reducedSource1372] using sourceEq1611 B hB

theorem rowSound1372 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1372 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1372, numericCheck1372, reducedZero1372 B hB hF, mul_zero]

theorem reducedZero1373 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1373 (mixedVector B) = 0 := by
  have h1127 : mixedVector B (Sum.inr 1127) = Sparse.eval nodeValue1127 (mixedVector B) := by
    change mixedMoment B node1127 node1127Labels = _
    exact sound1127 B hB hF
  have h1132 : mixedVector B (Sum.inr 1132) = Sparse.eval nodeValue1132 (mixedVector B) := by
    change mixedMoment B node1132 node1132Labels = _
    exact sound1132 B hB hF
  have h1134 : mixedVector B (Sum.inr 1134) = Sparse.eval nodeValue1134 (mixedVector B) := by
    change mixedMoment B node1134 node1134Labels = _
    exact sound1134 B hB hF
  have h1141 : mixedVector B (Sum.inr 1141) = Sparse.eval nodeValue1141 (mixedVector B) := by
    change mixedMoment B node1141 node1141Labels = _
    exact sound1141 B hB hF
  have h1237 : mixedVector B (Sum.inr 1237) = Sparse.eval nodeValue1237 (mixedVector B) := by
    change mixedMoment B node1237 node1237Labels = _
    exact sound1237 B hB hF
  have h2512 : mixedVector B (Sum.inr 2512) = Sparse.eval nodeValue2512 (mixedVector B) := by
    change mixedMoment B node2512 node2512Labels = _
    exact sound2512 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1612, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1127, h1132, h1134, h1141, h1237, h2512, h4092, reducedSource1373] using sourceEq1612 B hB

theorem rowSound1373 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1373 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1373, numericCheck1373, reducedZero1373 B hB hF, mul_zero]

theorem reducedZero1374 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1374 (mixedVector B) = 0 := by
  have h640 : mixedVector B (Sum.inr 640) = Sparse.eval nodeValue640 (mixedVector B) := by
    change mixedMoment B node640 node640Labels = _
    exact sound640 B hB hF
  have h1158 : mixedVector B (Sum.inr 1158) = Sparse.eval nodeValue1158 (mixedVector B) := by
    change mixedMoment B node1158 node1158Labels = _
    exact sound1158 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h1262 : mixedVector B (Sum.inr 1262) = Sparse.eval nodeValue1262 (mixedVector B) := by
    change mixedMoment B node1262 node1262Labels = _
    exact sound1262 B hB hF
  have h1293 : mixedVector B (Sum.inr 1293) = Sparse.eval nodeValue1293 (mixedVector B) := by
    change mixedMoment B node1293 node1293Labels = _
    exact sound1293 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1613, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h640, h1158, h1240, h1262, h1293, h4091, reducedSource1374] using sourceEq1613 B hB

theorem rowSound1374 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1374 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1374, numericCheck1374, reducedZero1374 B hB hF, mul_zero]

theorem reducedZero1375 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1375 (mixedVector B) = 0 := by
  have h1642 : mixedVector B (Sum.inr 1642) = Sparse.eval nodeValue1642 (mixedVector B) := by
    change mixedMoment B node1642 node1642Labels = _
    exact sound1642 B hB hF
  have h1645 : mixedVector B (Sum.inr 1645) = Sparse.eval nodeValue1645 (mixedVector B) := by
    change mixedMoment B node1645 node1645Labels = _
    exact sound1645 B hB hF
  have h1646 : mixedVector B (Sum.inr 1646) = Sparse.eval nodeValue1646 (mixedVector B) := by
    change mixedMoment B node1646 node1646Labels = _
    exact sound1646 B hB hF
  have h1649 : mixedVector B (Sum.inr 1649) = Sparse.eval nodeValue1649 (mixedVector B) := by
    change mixedMoment B node1649 node1649Labels = _
    exact sound1649 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1614, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1642, h1645, h1646, h1649, h1724, h3294, h4069, reducedSource1375] using sourceEq1614 B hB

theorem rowSound1375 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1375 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1375, numericCheck1375, reducedZero1375 B hB hF, mul_zero]

theorem sourceRowsAt1360 : MixedData.sourceRows (1360 : Fin 2425) =
    MixedData.row1360 := by decide +kernel

theorem sourceRowsAt1361 : MixedData.sourceRows (1361 : Fin 2425) =
    MixedData.row1361 := by decide +kernel

theorem sourceRowsAt1362 : MixedData.sourceRows (1362 : Fin 2425) =
    MixedData.row1362 := by decide +kernel

theorem sourceRowsAt1363 : MixedData.sourceRows (1363 : Fin 2425) =
    MixedData.row1363 := by decide +kernel

theorem sourceRowsAt1364 : MixedData.sourceRows (1364 : Fin 2425) =
    MixedData.row1364 := by decide +kernel

theorem sourceRowsAt1365 : MixedData.sourceRows (1365 : Fin 2425) =
    MixedData.row1365 := by decide +kernel

theorem sourceRowsAt1366 : MixedData.sourceRows (1366 : Fin 2425) =
    MixedData.row1366 := by decide +kernel

theorem sourceRowsAt1367 : MixedData.sourceRows (1367 : Fin 2425) =
    MixedData.row1367 := by decide +kernel

theorem sourceRowsAt1368 : MixedData.sourceRows (1368 : Fin 2425) =
    MixedData.row1368 := by decide +kernel

theorem sourceRowsAt1369 : MixedData.sourceRows (1369 : Fin 2425) =
    MixedData.row1369 := by decide +kernel

theorem sourceRowsAt1370 : MixedData.sourceRows (1370 : Fin 2425) =
    MixedData.row1370 := by decide +kernel

theorem sourceRowsAt1371 : MixedData.sourceRows (1371 : Fin 2425) =
    MixedData.row1371 := by decide +kernel

theorem sourceRowsAt1372 : MixedData.sourceRows (1372 : Fin 2425) =
    MixedData.row1372 := by decide +kernel

theorem sourceRowsAt1373 : MixedData.sourceRows (1373 : Fin 2425) =
    MixedData.row1373 := by decide +kernel

theorem sourceRowsAt1374 : MixedData.sourceRows (1374 : Fin 2425) =
    MixedData.row1374 := by decide +kernel

theorem sourceRowsAt1375 : MixedData.sourceRows (1375 : Fin 2425) =
    MixedData.row1375 := by decide +kernel

theorem chunkSound85 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 85) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1360 ∨ k.val = 1361 ∨ k.val = 1362 ∨ k.val = 1363 ∨ k.val = 1364 ∨ k.val = 1365 ∨ k.val = 1366 ∨ k.val = 1367 ∨ k.val = 1368 ∨ k.val = 1369 ∨ k.val = 1370 ∨ k.val = 1371 ∨ k.val = 1372 ∨ k.val = 1373 ∨ k.val = 1374 ∨ k.val = 1375 := by omega
  rcases heq with h1360 | h1361 | h1362 | h1363 | h1364 | h1365 | h1366 | h1367 | h1368 | h1369 | h1370 | h1371 | h1372 | h1373 | h1374 | h1375
  · have he : k = (1360 : Fin 2425) := Fin.ext h1360
    subst k
    rw [sourceRowsAt1360]
    exact rowSound1360 B hB hF
  · have he : k = (1361 : Fin 2425) := Fin.ext h1361
    subst k
    rw [sourceRowsAt1361]
    exact rowSound1361 B hB hF
  · have he : k = (1362 : Fin 2425) := Fin.ext h1362
    subst k
    rw [sourceRowsAt1362]
    exact rowSound1362 B hB hF
  · have he : k = (1363 : Fin 2425) := Fin.ext h1363
    subst k
    rw [sourceRowsAt1363]
    exact rowSound1363 B hB hF
  · have he : k = (1364 : Fin 2425) := Fin.ext h1364
    subst k
    rw [sourceRowsAt1364]
    exact rowSound1364 B hB hF
  · have he : k = (1365 : Fin 2425) := Fin.ext h1365
    subst k
    rw [sourceRowsAt1365]
    exact rowSound1365 B hB hF
  · have he : k = (1366 : Fin 2425) := Fin.ext h1366
    subst k
    rw [sourceRowsAt1366]
    exact rowSound1366 B hB hF
  · have he : k = (1367 : Fin 2425) := Fin.ext h1367
    subst k
    rw [sourceRowsAt1367]
    exact rowSound1367 B hB hF
  · have he : k = (1368 : Fin 2425) := Fin.ext h1368
    subst k
    rw [sourceRowsAt1368]
    exact rowSound1368 B hB hF
  · have he : k = (1369 : Fin 2425) := Fin.ext h1369
    subst k
    rw [sourceRowsAt1369]
    exact rowSound1369 B hB hF
  · have he : k = (1370 : Fin 2425) := Fin.ext h1370
    subst k
    rw [sourceRowsAt1370]
    exact rowSound1370 B hB hF
  · have he : k = (1371 : Fin 2425) := Fin.ext h1371
    subst k
    rw [sourceRowsAt1371]
    exact rowSound1371 B hB hF
  · have he : k = (1372 : Fin 2425) := Fin.ext h1372
    subst k
    rw [sourceRowsAt1372]
    exact rowSound1372 B hB hF
  · have he : k = (1373 : Fin 2425) := Fin.ext h1373
    subst k
    rw [sourceRowsAt1373]
    exact rowSound1373 B hB hF
  · have he : k = (1374 : Fin 2425) := Fin.ext h1374
    subst k
    rw [sourceRowsAt1374]
    exact rowSound1374 B hB hF
  · have he : k = (1375 : Fin 2425) := Fin.ext h1375
    subst k
    rw [sourceRowsAt1375]
    exact rowSound1375 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
