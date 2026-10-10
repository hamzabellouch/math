import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic133
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources84

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2128 (mixedVector B) = 0 := by
  have h1501 : mixedVector B (Sum.inr 1501) = Sparse.eval nodeValue1501 (mixedVector B) := by
    change mixedMoment B node1501 node1501Labels = _
    exact sound1501 B hB hF
  have h1503 : mixedVector B (Sum.inr 1503) = Sparse.eval nodeValue1503 (mixedVector B) := by
    change mixedMoment B node1503 node1503Labels = _
    exact sound1503 B hB hF
  have h1507 : mixedVector B (Sum.inr 1507) = Sparse.eval nodeValue1507 (mixedVector B) := by
    change mixedMoment B node1507 node1507Labels = _
    exact sound1507 B hB hF
  have h1524 : mixedVector B (Sum.inr 1524) = Sparse.eval nodeValue1524 (mixedVector B) := by
    change mixedMoment B node1524 node1524Labels = _
    exact sound1524 B hB hF
  have h4057 : mixedVector B (Sum.inr 4057) = Sparse.eval nodeValue4057 (mixedVector B) := by
    change mixedMoment B node4057 node4057Labels = _
    exact sound4057 B hB hF
  simpa only [sourceForm2687, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1501, h1503, h1507, h1524, h4057, reducedSource2128] using sourceEq2687 B hB

theorem rowSound2128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2128 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2128, numericCheck2128, reducedZero2128 B hB hF, mul_zero]

theorem reducedZero2129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2129 (mixedVector B) = 0 := by
  have h1504 : mixedVector B (Sum.inr 1504) = Sparse.eval nodeValue1504 (mixedVector B) := by
    change mixedMoment B node1504 node1504Labels = _
    exact sound1504 B hB hF
  have h1507 : mixedVector B (Sum.inr 1507) = Sparse.eval nodeValue1507 (mixedVector B) := by
    change mixedMoment B node1507 node1507Labels = _
    exact sound1507 B hB hF
  have h1508 : mixedVector B (Sum.inr 1508) = Sparse.eval nodeValue1508 (mixedVector B) := by
    change mixedMoment B node1508 node1508Labels = _
    exact sound1508 B hB hF
  have h1517 : mixedVector B (Sum.inr 1517) = Sparse.eval nodeValue1517 (mixedVector B) := by
    change mixedMoment B node1517 node1517Labels = _
    exact sound1517 B hB hF
  have h4057 : mixedVector B (Sum.inr 4057) = Sparse.eval nodeValue4057 (mixedVector B) := by
    change mixedMoment B node4057 node4057Labels = _
    exact sound4057 B hB hF
  simpa only [sourceForm2688, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1504, h1507, h1508, h1517, h4057, reducedSource2129] using sourceEq2688 B hB

theorem rowSound2129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2129 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2129, numericCheck2129, reducedZero2129 B hB hF, mul_zero]

theorem reducedZero2130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2130 (mixedVector B) = 0 := by
  have h1507 : mixedVector B (Sum.inr 1507) = Sparse.eval nodeValue1507 (mixedVector B) := by
    change mixedMoment B node1507 node1507Labels = _
    exact sound1507 B hB hF
  have h1510 : mixedVector B (Sum.inr 1510) = Sparse.eval nodeValue1510 (mixedVector B) := by
    change mixedMoment B node1510 node1510Labels = _
    exact sound1510 B hB hF
  have h1512 : mixedVector B (Sum.inr 1512) = Sparse.eval nodeValue1512 (mixedVector B) := by
    change mixedMoment B node1512 node1512Labels = _
    exact sound1512 B hB hF
  have h1517 : mixedVector B (Sum.inr 1517) = Sparse.eval nodeValue1517 (mixedVector B) := by
    change mixedMoment B node1517 node1517Labels = _
    exact sound1517 B hB hF
  have h1524 : mixedVector B (Sum.inr 1524) = Sparse.eval nodeValue1524 (mixedVector B) := by
    change mixedMoment B node1524 node1524Labels = _
    exact sound1524 B hB hF
  have h4057 : mixedVector B (Sum.inr 4057) = Sparse.eval nodeValue4057 (mixedVector B) := by
    change mixedMoment B node4057 node4057Labels = _
    exact sound4057 B hB hF
  simpa only [sourceForm2689, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1507, h1510, h1512, h1517, h1524, h4057, reducedSource2130] using sourceEq2689 B hB

theorem rowSound2130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2130 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2130, numericCheck2130, reducedZero2130 B hB hF, mul_zero]

theorem reducedZero2131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2131 (mixedVector B) = 0 := by
  have h687 : mixedVector B (Sum.inr 687) = Sparse.eval nodeValue687 (mixedVector B) := by
    change mixedMoment B node687 node687Labels = _
    exact sound687 B hB hF
  have h1491 : mixedVector B (Sum.inr 1491) = Sparse.eval nodeValue1491 (mixedVector B) := by
    change mixedMoment B node1491 node1491Labels = _
    exact sound1491 B hB hF
  have h1517 : mixedVector B (Sum.inr 1517) = Sparse.eval nodeValue1517 (mixedVector B) := by
    change mixedMoment B node1517 node1517Labels = _
    exact sound1517 B hB hF
  have h1524 : mixedVector B (Sum.inr 1524) = Sparse.eval nodeValue1524 (mixedVector B) := by
    change mixedMoment B node1524 node1524Labels = _
    exact sound1524 B hB hF
  have h4057 : mixedVector B (Sum.inr 4057) = Sparse.eval nodeValue4057 (mixedVector B) := by
    change mixedMoment B node4057 node4057Labels = _
    exact sound4057 B hB hF
  simpa only [sourceForm2691, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h687, h1491, h1517, h1524, h4057, reducedSource2131] using sourceEq2691 B hB

theorem rowSound2131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2131 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2131, numericCheck2131, reducedZero2131 B hB hF, mul_zero]

theorem reducedZero2132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2132 (mixedVector B) = 0 := by
  have h1502 : mixedVector B (Sum.inr 1502) = Sparse.eval nodeValue1502 (mixedVector B) := by
    change mixedMoment B node1502 node1502Labels = _
    exact sound1502 B hB hF
  have h1506 : mixedVector B (Sum.inr 1506) = Sparse.eval nodeValue1506 (mixedVector B) := by
    change mixedMoment B node1506 node1506Labels = _
    exact sound1506 B hB hF
  have h4056 : mixedVector B (Sum.inr 4056) = Sparse.eval nodeValue4056 (mixedVector B) := by
    change mixedMoment B node4056 node4056Labels = _
    exact sound4056 B hB hF
  simpa only [sourceForm2696, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1502, h1506, h4056, reducedSource2132] using sourceEq2696 B hB

theorem rowSound2132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2132 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2132, numericCheck2132, reducedZero2132 B hB hF, mul_zero]

theorem reducedZero2133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2133 (mixedVector B) = 0 := by
  have h666 : mixedVector B (Sum.inr 666) = Sparse.eval nodeValue666 (mixedVector B) := by
    change mixedMoment B node666 node666Labels = _
    exact sound666 B hB hF
  have h1497 : mixedVector B (Sum.inr 1497) = Sparse.eval nodeValue1497 (mixedVector B) := by
    change mixedMoment B node1497 node1497Labels = _
    exact sound1497 B hB hF
  have h1506 : mixedVector B (Sum.inr 1506) = Sparse.eval nodeValue1506 (mixedVector B) := by
    change mixedMoment B node1506 node1506Labels = _
    exact sound1506 B hB hF
  have h4056 : mixedVector B (Sum.inr 4056) = Sparse.eval nodeValue4056 (mixedVector B) := by
    change mixedMoment B node4056 node4056Labels = _
    exact sound4056 B hB hF
  simpa only [sourceForm2697, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h666, h1497, h1506, h4056, reducedSource2133] using sourceEq2697 B hB

theorem rowSound2133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2133 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2133, numericCheck2133, reducedZero2133 B hB hF, mul_zero]

theorem reducedZero2134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2134 (mixedVector B) = 0 := by
  have h1688 : mixedVector B (Sum.inr 1688) = Sparse.eval nodeValue1688 (mixedVector B) := by
    change mixedMoment B node1688 node1688Labels = _
    exact sound1688 B hB hF
  have h1692 : mixedVector B (Sum.inr 1692) = Sparse.eval nodeValue1692 (mixedVector B) := by
    change mixedMoment B node1692 node1692Labels = _
    exact sound1692 B hB hF
  have h1695 : mixedVector B (Sum.inr 1695) = Sparse.eval nodeValue1695 (mixedVector B) := by
    change mixedMoment B node1695 node1695Labels = _
    exact sound1695 B hB hF
  have h4066 : mixedVector B (Sum.inr 4066) = Sparse.eval nodeValue4066 (mixedVector B) := by
    change mixedMoment B node4066 node4066Labels = _
    exact sound4066 B hB hF
  simpa only [sourceForm2699, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1688, h1692, h1695, h4066, reducedSource2134] using sourceEq2699 B hB

theorem rowSound2134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2134 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2134, numericCheck2134, reducedZero2134 B hB hF, mul_zero]

theorem reducedZero2135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2135 (mixedVector B) = 0 := by
  have h1692 : mixedVector B (Sum.inr 1692) = Sparse.eval nodeValue1692 (mixedVector B) := by
    change mixedMoment B node1692 node1692Labels = _
    exact sound1692 B hB hF
  have h3262 : mixedVector B (Sum.inr 3262) = Sparse.eval nodeValue3262 (mixedVector B) := by
    change mixedMoment B node3262 node3262Labels = _
    exact sound3262 B hB hF
  have h3275 : mixedVector B (Sum.inr 3275) = Sparse.eval nodeValue3275 (mixedVector B) := by
    change mixedMoment B node3275 node3275Labels = _
    exact sound3275 B hB hF
  have h4066 : mixedVector B (Sum.inr 4066) = Sparse.eval nodeValue4066 (mixedVector B) := by
    change mixedMoment B node4066 node4066Labels = _
    exact sound4066 B hB hF
  simpa only [sourceForm2700, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1692, h3262, h3275, h4066, reducedSource2135] using sourceEq2700 B hB

theorem rowSound2135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2135 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2135, numericCheck2135, reducedZero2135 B hB hF, mul_zero]

theorem reducedZero2136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2136 (mixedVector B) = 0 := by
  have h1685 : mixedVector B (Sum.inr 1685) = Sparse.eval nodeValue1685 (mixedVector B) := by
    change mixedMoment B node1685 node1685Labels = _
    exact sound1685 B hB hF
  have h1687 : mixedVector B (Sum.inr 1687) = Sparse.eval nodeValue1687 (mixedVector B) := by
    change mixedMoment B node1687 node1687Labels = _
    exact sound1687 B hB hF
  have h1694 : mixedVector B (Sum.inr 1694) = Sparse.eval nodeValue1694 (mixedVector B) := by
    change mixedMoment B node1694 node1694Labels = _
    exact sound1694 B hB hF
  have h1743 : mixedVector B (Sum.inr 1743) = Sparse.eval nodeValue1743 (mixedVector B) := by
    change mixedMoment B node1743 node1743Labels = _
    exact sound1743 B hB hF
  have h2167 : mixedVector B (Sum.inr 2167) = Sparse.eval nodeValue2167 (mixedVector B) := by
    change mixedMoment B node2167 node2167Labels = _
    exact sound2167 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2703, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1685, h1687, h1694, h1743, h2167, h4067, reducedSource2136] using sourceEq2703 B hB

theorem rowSound2136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2136 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2136, numericCheck2136, reducedZero2136 B hB hF, mul_zero]

theorem reducedZero2137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2137 (mixedVector B) = 0 := by
  have h1679 : mixedVector B (Sum.inr 1679) = Sparse.eval nodeValue1679 (mixedVector B) := by
    change mixedMoment B node1679 node1679Labels = _
    exact sound1679 B hB hF
  have h1683 : mixedVector B (Sum.inr 1683) = Sparse.eval nodeValue1683 (mixedVector B) := by
    change mixedMoment B node1683 node1683Labels = _
    exact sound1683 B hB hF
  have h1693 : mixedVector B (Sum.inr 1693) = Sparse.eval nodeValue1693 (mixedVector B) := by
    change mixedMoment B node1693 node1693Labels = _
    exact sound1693 B hB hF
  have h1735 : mixedVector B (Sum.inr 1735) = Sparse.eval nodeValue1735 (mixedVector B) := by
    change mixedMoment B node1735 node1735Labels = _
    exact sound1735 B hB hF
  have h3277 : mixedVector B (Sum.inr 3277) = Sparse.eval nodeValue3277 (mixedVector B) := by
    change mixedMoment B node3277 node3277Labels = _
    exact sound3277 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2704, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1679, h1683, h1693, h1735, h3277, h4067, reducedSource2137] using sourceEq2704 B hB

theorem rowSound2137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2137 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2137, numericCheck2137, reducedZero2137 B hB hF, mul_zero]

theorem reducedZero2138 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2138 (mixedVector B) = 0 := by
  have h1689 : mixedVector B (Sum.inr 1689) = Sparse.eval nodeValue1689 (mixedVector B) := by
    change mixedMoment B node1689 node1689Labels = _
    exact sound1689 B hB hF
  have h1693 : mixedVector B (Sum.inr 1693) = Sparse.eval nodeValue1693 (mixedVector B) := by
    change mixedMoment B node1693 node1693Labels = _
    exact sound1693 B hB hF
  have h1694 : mixedVector B (Sum.inr 1694) = Sparse.eval nodeValue1694 (mixedVector B) := by
    change mixedMoment B node1694 node1694Labels = _
    exact sound1694 B hB hF
  have h1748 : mixedVector B (Sum.inr 1748) = Sparse.eval nodeValue1748 (mixedVector B) := by
    change mixedMoment B node1748 node1748Labels = _
    exact sound1748 B hB hF
  have h3276 : mixedVector B (Sum.inr 3276) = Sparse.eval nodeValue3276 (mixedVector B) := by
    change mixedMoment B node3276 node3276Labels = _
    exact sound3276 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2705, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1689, h1693, h1694, h1748, h3276, h4067, reducedSource2138] using sourceEq2705 B hB

theorem rowSound2138 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2138 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2138, numericCheck2138, reducedZero2138 B hB hF, mul_zero]

theorem reducedZero2139 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2139 (mixedVector B) = 0 := by
  have h1683 : mixedVector B (Sum.inr 1683) = Sparse.eval nodeValue1683 (mixedVector B) := by
    change mixedMoment B node1683 node1683Labels = _
    exact sound1683 B hB hF
  have h2149 : mixedVector B (Sum.inr 2149) = Sparse.eval nodeValue2149 (mixedVector B) := by
    change mixedMoment B node2149 node2149Labels = _
    exact sound2149 B hB hF
  have h2167 : mixedVector B (Sum.inr 2167) = Sparse.eval nodeValue2167 (mixedVector B) := by
    change mixedMoment B node2167 node2167Labels = _
    exact sound2167 B hB hF
  have h2258 : mixedVector B (Sum.inr 2258) = Sparse.eval nodeValue2258 (mixedVector B) := by
    change mixedMoment B node2258 node2258Labels = _
    exact sound2258 B hB hF
  have h3277 : mixedVector B (Sum.inr 3277) = Sparse.eval nodeValue3277 (mixedVector B) := by
    change mixedMoment B node3277 node3277Labels = _
    exact sound3277 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2706, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1683, h2149, h2167, h2258, h3277, h4067, reducedSource2139] using sourceEq2706 B hB

theorem rowSound2139 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2139 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2139, numericCheck2139, reducedZero2139 B hB hF, mul_zero]

theorem reducedZero2140 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2140 (mixedVector B) = 0 := by
  have h1694 : mixedVector B (Sum.inr 1694) = Sparse.eval nodeValue1694 (mixedVector B) := by
    change mixedMoment B node1694 node1694Labels = _
    exact sound1694 B hB hF
  have h2167 : mixedVector B (Sum.inr 2167) = Sparse.eval nodeValue2167 (mixedVector B) := by
    change mixedMoment B node2167 node2167Labels = _
    exact sound2167 B hB hF
  have h3268 : mixedVector B (Sum.inr 3268) = Sparse.eval nodeValue3268 (mixedVector B) := by
    change mixedMoment B node3268 node3268Labels = _
    exact sound3268 B hB hF
  have h3276 : mixedVector B (Sum.inr 3276) = Sparse.eval nodeValue3276 (mixedVector B) := by
    change mixedMoment B node3276 node3276Labels = _
    exact sound3276 B hB hF
  have h3277 : mixedVector B (Sum.inr 3277) = Sparse.eval nodeValue3277 (mixedVector B) := by
    change mixedMoment B node3277 node3277Labels = _
    exact sound3277 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2707, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1694, h2167, h3268, h3276, h3277, h4067, reducedSource2140] using sourceEq2707 B hB

theorem rowSound2140 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2140 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2140, numericCheck2140, reducedZero2140 B hB hF, mul_zero]

theorem reducedZero2141 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2141 (mixedVector B) = 0 := by
  have h1693 : mixedVector B (Sum.inr 1693) = Sparse.eval nodeValue1693 (mixedVector B) := by
    change mixedMoment B node1693 node1693Labels = _
    exact sound1693 B hB hF
  have h3272 : mixedVector B (Sum.inr 3272) = Sparse.eval nodeValue3272 (mixedVector B) := by
    change mixedMoment B node3272 node3272Labels = _
    exact sound3272 B hB hF
  have h3276 : mixedVector B (Sum.inr 3276) = Sparse.eval nodeValue3276 (mixedVector B) := by
    change mixedMoment B node3276 node3276Labels = _
    exact sound3276 B hB hF
  have h3277 : mixedVector B (Sum.inr 3277) = Sparse.eval nodeValue3277 (mixedVector B) := by
    change mixedMoment B node3277 node3277Labels = _
    exact sound3277 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2708, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1693, h3272, h3276, h3277, h4067, reducedSource2141] using sourceEq2708 B hB

theorem rowSound2141 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2141 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2141, numericCheck2141, reducedZero2141 B hB hF, mul_zero]

theorem reducedZero2142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2142 (mixedVector B) = 0 := by
  have h1579 : mixedVector B (Sum.inr 1579) = Sparse.eval nodeValue1579 (mixedVector B) := by
    change mixedMoment B node1579 node1579Labels = _
    exact sound1579 B hB hF
  have h3237 : mixedVector B (Sum.inr 3237) = Sparse.eval nodeValue3237 (mixedVector B) := by
    change mixedMoment B node3237 node3237Labels = _
    exact sound3237 B hB hF
  have h3252 : mixedVector B (Sum.inr 3252) = Sparse.eval nodeValue3252 (mixedVector B) := by
    change mixedMoment B node3252 node3252Labels = _
    exact sound3252 B hB hF
  have h3276 : mixedVector B (Sum.inr 3276) = Sparse.eval nodeValue3276 (mixedVector B) := by
    change mixedMoment B node3276 node3276Labels = _
    exact sound3276 B hB hF
  have h3277 : mixedVector B (Sum.inr 3277) = Sparse.eval nodeValue3277 (mixedVector B) := by
    change mixedMoment B node3277 node3277Labels = _
    exact sound3277 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2710, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1579, h3237, h3252, h3276, h3277, h4067, reducedSource2142] using sourceEq2710 B hB

theorem rowSound2142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2142 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2142, numericCheck2142, reducedZero2142 B hB hF, mul_zero]

theorem reducedZero2143 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2143 (mixedVector B) = 0 := by
  have h1576 : mixedVector B (Sum.inr 1576) = Sparse.eval nodeValue1576 (mixedVector B) := by
    change mixedMoment B node1576 node1576Labels = _
    exact sound1576 B hB hF
  have h1849 : mixedVector B (Sum.inr 1849) = Sparse.eval nodeValue1849 (mixedVector B) := by
    change mixedMoment B node1849 node1849Labels = _
    exact sound1849 B hB hF
  have h1858 : mixedVector B (Sum.inr 1858) = Sparse.eval nodeValue1858 (mixedVector B) := by
    change mixedMoment B node1858 node1858Labels = _
    exact sound1858 B hB hF
  have h2167 : mixedVector B (Sum.inr 2167) = Sparse.eval nodeValue2167 (mixedVector B) := by
    change mixedMoment B node2167 node2167Labels = _
    exact sound2167 B hB hF
  have h3276 : mixedVector B (Sum.inr 3276) = Sparse.eval nodeValue3276 (mixedVector B) := by
    change mixedMoment B node3276 node3276Labels = _
    exact sound3276 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  simpa only [sourceForm2712, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1576, h1849, h1858, h2167, h3276, h4067, reducedSource2143] using sourceEq2712 B hB

theorem rowSound2143 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2143 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2143, numericCheck2143, reducedZero2143 B hB hF, mul_zero]

theorem sourceRowsAt2128 : MixedData.sourceRows (2128 : Fin 2425) =
    MixedData.row2128 := by decide +kernel

theorem sourceRowsAt2129 : MixedData.sourceRows (2129 : Fin 2425) =
    MixedData.row2129 := by decide +kernel

theorem sourceRowsAt2130 : MixedData.sourceRows (2130 : Fin 2425) =
    MixedData.row2130 := by decide +kernel

theorem sourceRowsAt2131 : MixedData.sourceRows (2131 : Fin 2425) =
    MixedData.row2131 := by decide +kernel

theorem sourceRowsAt2132 : MixedData.sourceRows (2132 : Fin 2425) =
    MixedData.row2132 := by decide +kernel

theorem sourceRowsAt2133 : MixedData.sourceRows (2133 : Fin 2425) =
    MixedData.row2133 := by decide +kernel

theorem sourceRowsAt2134 : MixedData.sourceRows (2134 : Fin 2425) =
    MixedData.row2134 := by decide +kernel

theorem sourceRowsAt2135 : MixedData.sourceRows (2135 : Fin 2425) =
    MixedData.row2135 := by decide +kernel

theorem sourceRowsAt2136 : MixedData.sourceRows (2136 : Fin 2425) =
    MixedData.row2136 := by decide +kernel

theorem sourceRowsAt2137 : MixedData.sourceRows (2137 : Fin 2425) =
    MixedData.row2137 := by decide +kernel

theorem sourceRowsAt2138 : MixedData.sourceRows (2138 : Fin 2425) =
    MixedData.row2138 := by decide +kernel

theorem sourceRowsAt2139 : MixedData.sourceRows (2139 : Fin 2425) =
    MixedData.row2139 := by decide +kernel

theorem sourceRowsAt2140 : MixedData.sourceRows (2140 : Fin 2425) =
    MixedData.row2140 := by decide +kernel

theorem sourceRowsAt2141 : MixedData.sourceRows (2141 : Fin 2425) =
    MixedData.row2141 := by decide +kernel

theorem sourceRowsAt2142 : MixedData.sourceRows (2142 : Fin 2425) =
    MixedData.row2142 := by decide +kernel

theorem sourceRowsAt2143 : MixedData.sourceRows (2143 : Fin 2425) =
    MixedData.row2143 := by decide +kernel

theorem chunkSound133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 133) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2128 ∨ k.val = 2129 ∨ k.val = 2130 ∨ k.val = 2131 ∨ k.val = 2132 ∨ k.val = 2133 ∨ k.val = 2134 ∨ k.val = 2135 ∨ k.val = 2136 ∨ k.val = 2137 ∨ k.val = 2138 ∨ k.val = 2139 ∨ k.val = 2140 ∨ k.val = 2141 ∨ k.val = 2142 ∨ k.val = 2143 := by omega
  rcases heq with h2128 | h2129 | h2130 | h2131 | h2132 | h2133 | h2134 | h2135 | h2136 | h2137 | h2138 | h2139 | h2140 | h2141 | h2142 | h2143
  · have he : k = (2128 : Fin 2425) := Fin.ext h2128
    subst k
    rw [sourceRowsAt2128]
    exact rowSound2128 B hB hF
  · have he : k = (2129 : Fin 2425) := Fin.ext h2129
    subst k
    rw [sourceRowsAt2129]
    exact rowSound2129 B hB hF
  · have he : k = (2130 : Fin 2425) := Fin.ext h2130
    subst k
    rw [sourceRowsAt2130]
    exact rowSound2130 B hB hF
  · have he : k = (2131 : Fin 2425) := Fin.ext h2131
    subst k
    rw [sourceRowsAt2131]
    exact rowSound2131 B hB hF
  · have he : k = (2132 : Fin 2425) := Fin.ext h2132
    subst k
    rw [sourceRowsAt2132]
    exact rowSound2132 B hB hF
  · have he : k = (2133 : Fin 2425) := Fin.ext h2133
    subst k
    rw [sourceRowsAt2133]
    exact rowSound2133 B hB hF
  · have he : k = (2134 : Fin 2425) := Fin.ext h2134
    subst k
    rw [sourceRowsAt2134]
    exact rowSound2134 B hB hF
  · have he : k = (2135 : Fin 2425) := Fin.ext h2135
    subst k
    rw [sourceRowsAt2135]
    exact rowSound2135 B hB hF
  · have he : k = (2136 : Fin 2425) := Fin.ext h2136
    subst k
    rw [sourceRowsAt2136]
    exact rowSound2136 B hB hF
  · have he : k = (2137 : Fin 2425) := Fin.ext h2137
    subst k
    rw [sourceRowsAt2137]
    exact rowSound2137 B hB hF
  · have he : k = (2138 : Fin 2425) := Fin.ext h2138
    subst k
    rw [sourceRowsAt2138]
    exact rowSound2138 B hB hF
  · have he : k = (2139 : Fin 2425) := Fin.ext h2139
    subst k
    rw [sourceRowsAt2139]
    exact rowSound2139 B hB hF
  · have he : k = (2140 : Fin 2425) := Fin.ext h2140
    subst k
    rw [sourceRowsAt2140]
    exact rowSound2140 B hB hF
  · have he : k = (2141 : Fin 2425) := Fin.ext h2141
    subst k
    rw [sourceRowsAt2141]
    exact rowSound2141 B hB hF
  · have he : k = (2142 : Fin 2425) := Fin.ext h2142
    subst k
    rw [sourceRowsAt2142]
    exact rowSound2142 B hB hF
  · have he : k = (2143 : Fin 2425) := Fin.ext h2143
    subst k
    rw [sourceRowsAt2143]
    exact rowSound2143 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
