import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic97
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources57

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1552 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1552 (mixedVector B) = 0 := by
  have h1636 : mixedVector B (Sum.inr 1636) = Sparse.eval nodeValue1636 (mixedVector B) := by
    change mixedMoment B node1636 node1636Labels = _
    exact sound1636 B hB hF
  have h1638 : mixedVector B (Sum.inr 1638) = Sparse.eval nodeValue1638 (mixedVector B) := by
    change mixedMoment B node1638 node1638Labels = _
    exact sound1638 B hB hF
  have h1644 : mixedVector B (Sum.inr 1644) = Sparse.eval nodeValue1644 (mixedVector B) := by
    change mixedMoment B node1644 node1644Labels = _
    exact sound1644 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1835, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1636, h1638, h1644, h1706, h3289, h4068, reducedSource1552] using sourceEq1835 B hB

theorem rowSound1552 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1552 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1552, numericCheck1552, reducedZero1552 B hB hF, mul_zero]

theorem reducedZero1553 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1553 (mixedVector B) = 0 := by
  have h1593 : mixedVector B (Sum.inr 1593) = Sparse.eval nodeValue1593 (mixedVector B) := by
    change mixedMoment B node1593 node1593Labels = _
    exact sound1593 B hB hF
  have h1595 : mixedVector B (Sum.inr 1595) = Sparse.eval nodeValue1595 (mixedVector B) := by
    change mixedMoment B node1595 node1595Labels = _
    exact sound1595 B hB hF
  have h1600 : mixedVector B (Sum.inr 1600) = Sparse.eval nodeValue1600 (mixedVector B) := by
    change mixedMoment B node1600 node1600Labels = _
    exact sound1600 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1836, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1593, h1595, h1600, h1708, h3289, h4068, reducedSource1553] using sourceEq1836 B hB

theorem rowSound1553 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1553 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1553, numericCheck1553, reducedZero1553 B hB hF, mul_zero]

theorem reducedZero1554 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1554 (mixedVector B) = 0 := by
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3303 : mixedVector B (Sum.inr 3303) = Sparse.eval nodeValue3303 (mixedVector B) := by
    change mixedMoment B node3303 node3303Labels = _
    exact sound3303 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h3307 : mixedVector B (Sum.inr 3307) = Sparse.eval nodeValue3307 (mixedVector B) := by
    change mixedMoment B node3307 node3307Labels = _
    exact sound3307 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1837, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1708, h3289, h3303, h3304, h3307, h4068, reducedSource1554] using sourceEq1837 B hB

theorem rowSound1554 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1554 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1554, numericCheck1554, reducedZero1554 B hB hF, mul_zero]

theorem reducedZero1555 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1555 (mixedVector B) = 0 := by
  have h1600 : mixedVector B (Sum.inr 1600) = Sparse.eval nodeValue1600 (mixedVector B) := by
    change mixedMoment B node1600 node1600Labels = _
    exact sound1600 B hB hF
  have h3239 : mixedVector B (Sum.inr 3239) = Sparse.eval nodeValue3239 (mixedVector B) := by
    change mixedMoment B node3239 node3239Labels = _
    exact sound3239 B hB hF
  have h3286 : mixedVector B (Sum.inr 3286) = Sparse.eval nodeValue3286 (mixedVector B) := by
    change mixedMoment B node3286 node3286Labels = _
    exact sound3286 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3292 : mixedVector B (Sum.inr 3292) = Sparse.eval nodeValue3292 (mixedVector B) := by
    change mixedMoment B node3292 node3292Labels = _
    exact sound3292 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1838, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1600, h3239, h3286, h3289, h3292, h4068, reducedSource1555] using sourceEq1838 B hB

theorem rowSound1555 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1555 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1555, numericCheck1555, reducedZero1555 B hB hF, mul_zero]

theorem reducedZero1556 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1556 (mixedVector B) = 0 := by
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3292 : mixedVector B (Sum.inr 3292) = Sparse.eval nodeValue3292 (mixedVector B) := by
    change mixedMoment B node3292 node3292Labels = _
    exact sound3292 B hB hF
  have h3307 : mixedVector B (Sum.inr 3307) = Sparse.eval nodeValue3307 (mixedVector B) := by
    change mixedMoment B node3307 node3307Labels = _
    exact sound3307 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1839, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1706, h3289, h3292, h3307, h4068, reducedSource1556] using sourceEq1839 B hB

theorem rowSound1556 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1556 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1556, numericCheck1556, reducedZero1556 B hB hF, mul_zero]

theorem reducedZero1557 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1557 (mixedVector B) = 0 := by
  have h1648 : mixedVector B (Sum.inr 1648) = Sparse.eval nodeValue1648 (mixedVector B) := by
    change mixedMoment B node1648 node1648Labels = _
    exact sound1648 B hB hF
  have h3072 : mixedVector B (Sum.inr 3072) = Sparse.eval nodeValue3072 (mixedVector B) := by
    change mixedMoment B node3072 node3072Labels = _
    exact sound3072 B hB hF
  have h3286 : mixedVector B (Sum.inr 3286) = Sparse.eval nodeValue3286 (mixedVector B) := by
    change mixedMoment B node3286 node3286Labels = _
    exact sound3286 B hB hF
  have h3303 : mixedVector B (Sum.inr 3303) = Sparse.eval nodeValue3303 (mixedVector B) := by
    change mixedMoment B node3303 node3303Labels = _
    exact sound3303 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1841, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1648, h3072, h3286, h3303, h3304, h4068, reducedSource1557] using sourceEq1841 B hB

theorem rowSound1557 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1557 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1557, numericCheck1557, reducedZero1557 B hB hF, mul_zero]

theorem reducedZero1558 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1558 (mixedVector B) = 0 := by
  have h1636 : mixedVector B (Sum.inr 1636) = Sparse.eval nodeValue1636 (mixedVector B) := by
    change mixedMoment B node1636 node1636Labels = _
    exact sound1636 B hB hF
  have h1639 : mixedVector B (Sum.inr 1639) = Sparse.eval nodeValue1639 (mixedVector B) := by
    change mixedMoment B node1639 node1639Labels = _
    exact sound1639 B hB hF
  have h1641 : mixedVector B (Sum.inr 1641) = Sparse.eval nodeValue1641 (mixedVector B) := by
    change mixedMoment B node1641 node1641Labels = _
    exact sound1641 B hB hF
  have h1648 : mixedVector B (Sum.inr 1648) = Sparse.eval nodeValue1648 (mixedVector B) := by
    change mixedMoment B node1648 node1648Labels = _
    exact sound1648 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h3303 : mixedVector B (Sum.inr 3303) = Sparse.eval nodeValue3303 (mixedVector B) := by
    change mixedMoment B node3303 node3303Labels = _
    exact sound3303 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1842, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1636, h1639, h1641, h1648, h1708, h3303, h4068, reducedSource1558] using sourceEq1842 B hB

theorem rowSound1558 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1558 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1558, numericCheck1558, reducedZero1558 B hB hF, mul_zero]

theorem reducedZero1559 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1559 (mixedVector B) = 0 := by
  have h4164 : mixedVector B (Sum.inr 4164) = Sparse.eval nodeValue4164 (mixedVector B) := by
    change mixedMoment B node4164 node4164Labels = _
    exact sound4164 B hB hF
  have h4165 : mixedVector B (Sum.inr 4165) = Sparse.eval nodeValue4165 (mixedVector B) := by
    change mixedMoment B node4165 node4165Labels = _
    exact sound4165 B hB hF
  have h4182 : mixedVector B (Sum.inr 4182) = Sparse.eval nodeValue4182 (mixedVector B) := by
    change mixedMoment B node4182 node4182Labels = _
    exact sound4182 B hB hF
  have h4537 : mixedVector B (Sum.inr 4537) = Sparse.eval nodeValue4537 (mixedVector B) := by
    change mixedMoment B node4537 node4537Labels = _
    exact sound4537 B hB hF
  have h4550 : mixedVector B (Sum.inr 4550) = Sparse.eval nodeValue4550 (mixedVector B) := by
    change mixedMoment B node4550 node4550Labels = _
    exact sound4550 B hB hF
  have h4569 : mixedVector B (Sum.inr 4569) = Sparse.eval nodeValue4569 (mixedVector B) := by
    change mixedMoment B node4569 node4569Labels = _
    exact sound4569 B hB hF
  have h4570 : mixedVector B (Sum.inr 4570) = Sparse.eval nodeValue4570 (mixedVector B) := by
    change mixedMoment B node4570 node4570Labels = _
    exact sound4570 B hB hF
  have h4618 : mixedVector B (Sum.inr 4618) = Sparse.eval nodeValue4618 (mixedVector B) := by
    change mixedMoment B node4618 node4618Labels = _
    exact sound4618 B hB hF
  have h4619 : mixedVector B (Sum.inr 4619) = Sparse.eval nodeValue4619 (mixedVector B) := by
    change mixedMoment B node4619 node4619Labels = _
    exact sound4619 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h5166 : mixedVector B (Sum.inr 5166) = Sparse.eval nodeValue5166 (mixedVector B) := by
    change mixedMoment B node5166 node5166Labels = _
    exact sound5166 B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  simpa only [sourceForm1843, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4164, h4165, h4182, h4537, h4550, h4569, h4570, h4618, h4619, h4623, h5166, h5301, h5306, reducedSource1559] using sourceEq1843 B hB

theorem rowSound1559 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1559 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1559, numericCheck1559, reducedZero1559 B hB hF, mul_zero]

theorem reducedZero1560 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1560 (mixedVector B) = 0 := by
  have h592 : mixedVector B (Sum.inr 592) = Sparse.eval nodeValue592 (mixedVector B) := by
    change mixedMoment B node592 node592Labels = _
    exact sound592 B hB hF
  have h593 : mixedVector B (Sum.inr 593) = Sparse.eval nodeValue593 (mixedVector B) := by
    change mixedMoment B node593 node593Labels = _
    exact sound593 B hB hF
  have h610 : mixedVector B (Sum.inr 610) = Sparse.eval nodeValue610 (mixedVector B) := by
    change mixedMoment B node610 node610Labels = _
    exact sound610 B hB hF
  have h1122 : mixedVector B (Sum.inr 1122) = Sparse.eval nodeValue1122 (mixedVector B) := by
    change mixedMoment B node1122 node1122Labels = _
    exact sound1122 B hB hF
  have h1135 : mixedVector B (Sum.inr 1135) = Sparse.eval nodeValue1135 (mixedVector B) := by
    change mixedMoment B node1135 node1135Labels = _
    exact sound1135 B hB hF
  have h1187 : mixedVector B (Sum.inr 1187) = Sparse.eval nodeValue1187 (mixedVector B) := by
    change mixedMoment B node1187 node1187Labels = _
    exact sound1187 B hB hF
  have h1188 : mixedVector B (Sum.inr 1188) = Sparse.eval nodeValue1188 (mixedVector B) := by
    change mixedMoment B node1188 node1188Labels = _
    exact sound1188 B hB hF
  have h1293 : mixedVector B (Sum.inr 1293) = Sparse.eval nodeValue1293 (mixedVector B) := by
    change mixedMoment B node1293 node1293Labels = _
    exact sound1293 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h1305 : mixedVector B (Sum.inr 1305) = Sparse.eval nodeValue1305 (mixedVector B) := by
    change mixedMoment B node1305 node1305Labels = _
    exact sound1305 B hB hF
  have h2953 : mixedVector B (Sum.inr 2953) = Sparse.eval nodeValue2953 (mixedVector B) := by
    change mixedMoment B node2953 node2953Labels = _
    exact sound2953 B hB hF
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  have h3120 : mixedVector B (Sum.inr 3120) = Sparse.eval nodeValue3120 (mixedVector B) := by
    change mixedMoment B node3120 node3120Labels = _
    exact sound3120 B hB hF
  simpa only [sourceForm1844, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h592, h593, h610, h1122, h1135, h1187, h1188, h1293, h1294, h1305, h2953, h3053, h3120, reducedSource1560] using sourceEq1844 B hB

theorem rowSound1560 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1560 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1560, numericCheck1560, reducedZero1560 B hB hF, mul_zero]

theorem reducedZero1561 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1561 (mixedVector B) = 0 := by
  have h4169 : mixedVector B (Sum.inr 4169) = Sparse.eval nodeValue4169 (mixedVector B) := by
    change mixedMoment B node4169 node4169Labels = _
    exact sound4169 B hB hF
  have h4170 : mixedVector B (Sum.inr 4170) = Sparse.eval nodeValue4170 (mixedVector B) := by
    change mixedMoment B node4170 node4170Labels = _
    exact sound4170 B hB hF
  have h4173 : mixedVector B (Sum.inr 4173) = Sparse.eval nodeValue4173 (mixedVector B) := by
    change mixedMoment B node4173 node4173Labels = _
    exact sound4173 B hB hF
  have h4540 : mixedVector B (Sum.inr 4540) = Sparse.eval nodeValue4540 (mixedVector B) := by
    change mixedMoment B node4540 node4540Labels = _
    exact sound4540 B hB hF
  have h4542 : mixedVector B (Sum.inr 4542) = Sparse.eval nodeValue4542 (mixedVector B) := by
    change mixedMoment B node4542 node4542Labels = _
    exact sound4542 B hB hF
  have h4599 : mixedVector B (Sum.inr 4599) = Sparse.eval nodeValue4599 (mixedVector B) := by
    change mixedMoment B node4599 node4599Labels = _
    exact sound4599 B hB hF
  have h4600 : mixedVector B (Sum.inr 4600) = Sparse.eval nodeValue4600 (mixedVector B) := by
    change mixedMoment B node4600 node4600Labels = _
    exact sound4600 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h4603 : mixedVector B (Sum.inr 4603) = Sparse.eval nodeValue4603 (mixedVector B) := by
    change mixedMoment B node4603 node4603Labels = _
    exact sound4603 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h5162 : mixedVector B (Sum.inr 5162) = Sparse.eval nodeValue5162 (mixedVector B) := by
    change mixedMoment B node5162 node5162Labels = _
    exact sound5162 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  simpa only [sourceForm1845, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4169, h4170, h4173, h4540, h4542, h4599, h4600, h4601, h4603, h4606, h5162, h5273, h5290, reducedSource1561] using sourceEq1845 B hB

theorem rowSound1561 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1561 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1561, numericCheck1561, reducedZero1561 B hB hF, mul_zero]

theorem reducedZero1562 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1562 (mixedVector B) = 0 := by
  have h597 : mixedVector B (Sum.inr 597) = Sparse.eval nodeValue597 (mixedVector B) := by
    change mixedMoment B node597 node597Labels = _
    exact sound597 B hB hF
  have h598 : mixedVector B (Sum.inr 598) = Sparse.eval nodeValue598 (mixedVector B) := by
    change mixedMoment B node598 node598Labels = _
    exact sound598 B hB hF
  have h601 : mixedVector B (Sum.inr 601) = Sparse.eval nodeValue601 (mixedVector B) := by
    change mixedMoment B node601 node601Labels = _
    exact sound601 B hB hF
  have h1125 : mixedVector B (Sum.inr 1125) = Sparse.eval nodeValue1125 (mixedVector B) := by
    change mixedMoment B node1125 node1125Labels = _
    exact sound1125 B hB hF
  have h1127 : mixedVector B (Sum.inr 1127) = Sparse.eval nodeValue1127 (mixedVector B) := by
    change mixedMoment B node1127 node1127Labels = _
    exact sound1127 B hB hF
  have h1233 : mixedVector B (Sum.inr 1233) = Sparse.eval nodeValue1233 (mixedVector B) := by
    change mixedMoment B node1233 node1233Labels = _
    exact sound1233 B hB hF
  have h1234 : mixedVector B (Sum.inr 1234) = Sparse.eval nodeValue1234 (mixedVector B) := by
    change mixedMoment B node1234 node1234Labels = _
    exact sound1234 B hB hF
  have h1237 : mixedVector B (Sum.inr 1237) = Sparse.eval nodeValue1237 (mixedVector B) := by
    change mixedMoment B node1237 node1237Labels = _
    exact sound1237 B hB hF
  have h1265 : mixedVector B (Sum.inr 1265) = Sparse.eval nodeValue1265 (mixedVector B) := by
    change mixedMoment B node1265 node1265Labels = _
    exact sound1265 B hB hF
  have h1266 : mixedVector B (Sum.inr 1266) = Sparse.eval nodeValue1266 (mixedVector B) := by
    change mixedMoment B node1266 node1266Labels = _
    exact sound1266 B hB hF
  have h2957 : mixedVector B (Sum.inr 2957) = Sparse.eval nodeValue2957 (mixedVector B) := by
    change mixedMoment B node2957 node2957Labels = _
    exact sound2957 B hB hF
  have h3099 : mixedVector B (Sum.inr 3099) = Sparse.eval nodeValue3099 (mixedVector B) := by
    change mixedMoment B node3099 node3099Labels = _
    exact sound3099 B hB hF
  have h3111 : mixedVector B (Sum.inr 3111) = Sparse.eval nodeValue3111 (mixedVector B) := by
    change mixedMoment B node3111 node3111Labels = _
    exact sound3111 B hB hF
  simpa only [sourceForm1846, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h597, h598, h601, h1125, h1127, h1233, h1234, h1237, h1265, h1266, h2957, h3099, h3111, reducedSource1562] using sourceEq1846 B hB

theorem rowSound1562 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1562 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1562, numericCheck1562, reducedZero1562 B hB hF, mul_zero]

theorem reducedZero1563 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1563 (mixedVector B) = 0 := by
  have h1502 : mixedVector B (Sum.inr 1502) = Sparse.eval nodeValue1502 (mixedVector B) := by
    change mixedMoment B node1502 node1502Labels = _
    exact sound1502 B hB hF
  have h1503 : mixedVector B (Sum.inr 1503) = Sparse.eval nodeValue1503 (mixedVector B) := by
    change mixedMoment B node1503 node1503Labels = _
    exact sound1503 B hB hF
  have h1508 : mixedVector B (Sum.inr 1508) = Sparse.eval nodeValue1508 (mixedVector B) := by
    change mixedMoment B node1508 node1508Labels = _
    exact sound1508 B hB hF
  have h2688 : mixedVector B (Sum.inr 2688) = Sparse.eval nodeValue2688 (mixedVector B) := by
    change mixedMoment B node2688 node2688Labels = _
    exact sound2688 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h3257 : mixedVector B (Sum.inr 3257) = Sparse.eval nodeValue3257 (mixedVector B) := by
    change mixedMoment B node3257 node3257Labels = _
    exact sound3257 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3292 : mixedVector B (Sum.inr 3292) = Sparse.eval nodeValue3292 (mixedVector B) := by
    change mixedMoment B node3292 node3292Labels = _
    exact sound3292 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h3546 : mixedVector B (Sum.inr 3546) = Sparse.eval nodeValue3546 (mixedVector B) := by
    change mixedMoment B node3546 node3546Labels = _
    exact sound3546 B hB hF
  have h3563 : mixedVector B (Sum.inr 3563) = Sparse.eval nodeValue3563 (mixedVector B) := by
    change mixedMoment B node3563 node3563Labels = _
    exact sound3563 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  simpa only [sourceForm1847, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1502, h1503, h1508, h2688, h2702, h3257, h3289, h3292, h3294, h3299, h3546, h3563, h3581, reducedSource1563] using sourceEq1847 B hB

theorem rowSound1563 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1563 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1563, numericCheck1563, reducedZero1563 B hB hF, mul_zero]

theorem reducedZero1564 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1564 (mixedVector B) = 0 := by
  have h637 : mixedVector B (Sum.inr 637) = Sparse.eval nodeValue637 (mixedVector B) := by
    change mixedMoment B node637 node637Labels = _
    exact sound637 B hB hF
  have h640 : mixedVector B (Sum.inr 640) = Sparse.eval nodeValue640 (mixedVector B) := by
    change mixedMoment B node640 node640Labels = _
    exact sound640 B hB hF
  have h651 : mixedVector B (Sum.inr 651) = Sparse.eval nodeValue651 (mixedVector B) := by
    change mixedMoment B node651 node651Labels = _
    exact sound651 B hB hF
  have h1293 : mixedVector B (Sum.inr 1293) = Sparse.eval nodeValue1293 (mixedVector B) := by
    change mixedMoment B node1293 node1293Labels = _
    exact sound1293 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1848, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h637, h640, h651, h1293, h4091, reducedSource1564] using sourceEq1848 B hB

theorem rowSound1564 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1564 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1564, numericCheck1564, reducedZero1564 B hB hF, mul_zero]

theorem reducedZero1565 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1565 (mixedVector B) = 0 := by
  have h1034 : mixedVector B (Sum.inr 1034) = Sparse.eval nodeValue1034 (mixedVector B) := by
    change mixedMoment B node1034 node1034Labels = _
    exact sound1034 B hB hF
  have h1073 : mixedVector B (Sum.inr 1073) = Sparse.eval nodeValue1073 (mixedVector B) := by
    change mixedMoment B node1073 node1073Labels = _
    exact sound1073 B hB hF
  have h1081 : mixedVector B (Sum.inr 1081) = Sparse.eval nodeValue1081 (mixedVector B) := by
    change mixedMoment B node1081 node1081Labels = _
    exact sound1081 B hB hF
  have h1228 : mixedVector B (Sum.inr 1228) = Sparse.eval nodeValue1228 (mixedVector B) := by
    change mixedMoment B node1228 node1228Labels = _
    exact sound1228 B hB hF
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h1256 : mixedVector B (Sum.inr 1256) = Sparse.eval nodeValue1256 (mixedVector B) := by
    change mixedMoment B node1256 node1256Labels = _
    exact sound1256 B hB hF
  have h1260 : mixedVector B (Sum.inr 1260) = Sparse.eval nodeValue1260 (mixedVector B) := by
    change mixedMoment B node1260 node1260Labels = _
    exact sound1260 B hB hF
  have h1286 : mixedVector B (Sum.inr 1286) = Sparse.eval nodeValue1286 (mixedVector B) := by
    change mixedMoment B node1286 node1286Labels = _
    exact sound1286 B hB hF
  have h1291 : mixedVector B (Sum.inr 1291) = Sparse.eval nodeValue1291 (mixedVector B) := by
    change mixedMoment B node1291 node1291Labels = _
    exact sound1291 B hB hF
  have h1299 : mixedVector B (Sum.inr 1299) = Sparse.eval nodeValue1299 (mixedVector B) := by
    change mixedMoment B node1299 node1299Labels = _
    exact sound1299 B hB hF
  have h1405 : mixedVector B (Sum.inr 1405) = Sparse.eval nodeValue1405 (mixedVector B) := by
    change mixedMoment B node1405 node1405Labels = _
    exact sound1405 B hB hF
  have h1435 : mixedVector B (Sum.inr 1435) = Sparse.eval nodeValue1435 (mixedVector B) := by
    change mixedMoment B node1435 node1435Labels = _
    exact sound1435 B hB hF
  have h1441 : mixedVector B (Sum.inr 1441) = Sparse.eval nodeValue1441 (mixedVector B) := by
    change mixedMoment B node1441 node1441Labels = _
    exact sound1441 B hB hF
  simpa only [sourceForm1850, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1034, h1073, h1081, h1228, h1235, h1256, h1260, h1286, h1291, h1299, h1405, h1435, h1441, reducedSource1565] using sourceEq1850 B hB

theorem rowSound1565 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1565 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1565, numericCheck1565, reducedZero1565 B hB hF, mul_zero]

theorem reducedZero1566 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1566 (mixedVector B) = 0 := by
  have h1644 : mixedVector B (Sum.inr 1644) = Sparse.eval nodeValue1644 (mixedVector B) := by
    change mixedMoment B node1644 node1644Labels = _
    exact sound1644 B hB hF
  have h1648 : mixedVector B (Sum.inr 1648) = Sparse.eval nodeValue1648 (mixedVector B) := by
    change mixedMoment B node1648 node1648Labels = _
    exact sound1648 B hB hF
  have h1726 : mixedVector B (Sum.inr 1726) = Sparse.eval nodeValue1726 (mixedVector B) := by
    change mixedMoment B node1726 node1726Labels = _
    exact sound1726 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1851, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1644, h1648, h1726, h3304, h4068, reducedSource1566] using sourceEq1851 B hB

theorem rowSound1566 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1566 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1566, numericCheck1566, reducedZero1566 B hB hF, mul_zero]

theorem reducedZero1567 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1567 (mixedVector B) = 0 := by
  have h4171 : mixedVector B (Sum.inr 4171) = Sparse.eval nodeValue4171 (mixedVector B) := by
    change mixedMoment B node4171 node4171Labels = _
    exact sound4171 B hB hF
  have h4172 : mixedVector B (Sum.inr 4172) = Sparse.eval nodeValue4172 (mixedVector B) := by
    change mixedMoment B node4172 node4172Labels = _
    exact sound4172 B hB hF
  have h4175 : mixedVector B (Sum.inr 4175) = Sparse.eval nodeValue4175 (mixedVector B) := by
    change mixedMoment B node4175 node4175Labels = _
    exact sound4175 B hB hF
  have h4541 : mixedVector B (Sum.inr 4541) = Sparse.eval nodeValue4541 (mixedVector B) := by
    change mixedMoment B node4541 node4541Labels = _
    exact sound4541 B hB hF
  have h4544 : mixedVector B (Sum.inr 4544) = Sparse.eval nodeValue4544 (mixedVector B) := by
    change mixedMoment B node4544 node4544Labels = _
    exact sound4544 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4622 : mixedVector B (Sum.inr 4622) = Sparse.eval nodeValue4622 (mixedVector B) := by
    change mixedMoment B node4622 node4622Labels = _
    exact sound4622 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h4624 : mixedVector B (Sum.inr 4624) = Sparse.eval nodeValue4624 (mixedVector B) := by
    change mixedMoment B node4624 node4624Labels = _
    exact sound4624 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5307 : mixedVector B (Sum.inr 5307) = Sparse.eval nodeValue5307 (mixedVector B) := by
    change mixedMoment B node5307 node5307Labels = _
    exact sound5307 B hB hF
  simpa only [sourceForm1852, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4171, h4172, h4175, h4541, h4544, h4601, h4602, h4606, h4622, h4623, h4624, h5167, h5292, h5307, reducedSource1567] using sourceEq1852 B hB

theorem rowSound1567 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1567 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1567, numericCheck1567, reducedZero1567 B hB hF, mul_zero]

theorem sourceRowsAt1552 : MixedData.sourceRows (1552 : Fin 2425) =
    MixedData.row1552 := by decide +kernel

theorem sourceRowsAt1553 : MixedData.sourceRows (1553 : Fin 2425) =
    MixedData.row1553 := by decide +kernel

theorem sourceRowsAt1554 : MixedData.sourceRows (1554 : Fin 2425) =
    MixedData.row1554 := by decide +kernel

theorem sourceRowsAt1555 : MixedData.sourceRows (1555 : Fin 2425) =
    MixedData.row1555 := by decide +kernel

theorem sourceRowsAt1556 : MixedData.sourceRows (1556 : Fin 2425) =
    MixedData.row1556 := by decide +kernel

theorem sourceRowsAt1557 : MixedData.sourceRows (1557 : Fin 2425) =
    MixedData.row1557 := by decide +kernel

theorem sourceRowsAt1558 : MixedData.sourceRows (1558 : Fin 2425) =
    MixedData.row1558 := by decide +kernel

theorem sourceRowsAt1559 : MixedData.sourceRows (1559 : Fin 2425) =
    MixedData.row1559 := by decide +kernel

theorem sourceRowsAt1560 : MixedData.sourceRows (1560 : Fin 2425) =
    MixedData.row1560 := by decide +kernel

theorem sourceRowsAt1561 : MixedData.sourceRows (1561 : Fin 2425) =
    MixedData.row1561 := by decide +kernel

theorem sourceRowsAt1562 : MixedData.sourceRows (1562 : Fin 2425) =
    MixedData.row1562 := by decide +kernel

theorem sourceRowsAt1563 : MixedData.sourceRows (1563 : Fin 2425) =
    MixedData.row1563 := by decide +kernel

theorem sourceRowsAt1564 : MixedData.sourceRows (1564 : Fin 2425) =
    MixedData.row1564 := by decide +kernel

theorem sourceRowsAt1565 : MixedData.sourceRows (1565 : Fin 2425) =
    MixedData.row1565 := by decide +kernel

theorem sourceRowsAt1566 : MixedData.sourceRows (1566 : Fin 2425) =
    MixedData.row1566 := by decide +kernel

theorem sourceRowsAt1567 : MixedData.sourceRows (1567 : Fin 2425) =
    MixedData.row1567 := by decide +kernel

theorem chunkSound97 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 97) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1552 ∨ k.val = 1553 ∨ k.val = 1554 ∨ k.val = 1555 ∨ k.val = 1556 ∨ k.val = 1557 ∨ k.val = 1558 ∨ k.val = 1559 ∨ k.val = 1560 ∨ k.val = 1561 ∨ k.val = 1562 ∨ k.val = 1563 ∨ k.val = 1564 ∨ k.val = 1565 ∨ k.val = 1566 ∨ k.val = 1567 := by omega
  rcases heq with h1552 | h1553 | h1554 | h1555 | h1556 | h1557 | h1558 | h1559 | h1560 | h1561 | h1562 | h1563 | h1564 | h1565 | h1566 | h1567
  · have he : k = (1552 : Fin 2425) := Fin.ext h1552
    subst k
    rw [sourceRowsAt1552]
    exact rowSound1552 B hB hF
  · have he : k = (1553 : Fin 2425) := Fin.ext h1553
    subst k
    rw [sourceRowsAt1553]
    exact rowSound1553 B hB hF
  · have he : k = (1554 : Fin 2425) := Fin.ext h1554
    subst k
    rw [sourceRowsAt1554]
    exact rowSound1554 B hB hF
  · have he : k = (1555 : Fin 2425) := Fin.ext h1555
    subst k
    rw [sourceRowsAt1555]
    exact rowSound1555 B hB hF
  · have he : k = (1556 : Fin 2425) := Fin.ext h1556
    subst k
    rw [sourceRowsAt1556]
    exact rowSound1556 B hB hF
  · have he : k = (1557 : Fin 2425) := Fin.ext h1557
    subst k
    rw [sourceRowsAt1557]
    exact rowSound1557 B hB hF
  · have he : k = (1558 : Fin 2425) := Fin.ext h1558
    subst k
    rw [sourceRowsAt1558]
    exact rowSound1558 B hB hF
  · have he : k = (1559 : Fin 2425) := Fin.ext h1559
    subst k
    rw [sourceRowsAt1559]
    exact rowSound1559 B hB hF
  · have he : k = (1560 : Fin 2425) := Fin.ext h1560
    subst k
    rw [sourceRowsAt1560]
    exact rowSound1560 B hB hF
  · have he : k = (1561 : Fin 2425) := Fin.ext h1561
    subst k
    rw [sourceRowsAt1561]
    exact rowSound1561 B hB hF
  · have he : k = (1562 : Fin 2425) := Fin.ext h1562
    subst k
    rw [sourceRowsAt1562]
    exact rowSound1562 B hB hF
  · have he : k = (1563 : Fin 2425) := Fin.ext h1563
    subst k
    rw [sourceRowsAt1563]
    exact rowSound1563 B hB hF
  · have he : k = (1564 : Fin 2425) := Fin.ext h1564
    subst k
    rw [sourceRowsAt1564]
    exact rowSound1564 B hB hF
  · have he : k = (1565 : Fin 2425) := Fin.ext h1565
    subst k
    rw [sourceRowsAt1565]
    exact rowSound1565 B hB hF
  · have he : k = (1566 : Fin 2425) := Fin.ext h1566
    subst k
    rw [sourceRowsAt1566]
    exact rowSound1566 B hB hF
  · have he : k = (1567 : Fin 2425) := Fin.ext h1567
    subst k
    rw [sourceRowsAt1567]
    exact rowSound1567 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
