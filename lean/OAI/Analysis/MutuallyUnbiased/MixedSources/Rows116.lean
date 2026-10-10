import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic116
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources71

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1856 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1856 (mixedVector B) = 0 := by
  have h1641 : mixedVector B (Sum.inr 1641) = Sparse.eval nodeValue1641 (mixedVector B) := by
    change mixedMoment B node1641 node1641Labels = _
    exact sound1641 B hB hF
  have h1653 : mixedVector B (Sum.inr 1653) = Sparse.eval nodeValue1653 (mixedVector B) := by
    change mixedMoment B node1653 node1653Labels = _
    exact sound1653 B hB hF
  have h1661 : mixedVector B (Sum.inr 1661) = Sparse.eval nodeValue1661 (mixedVector B) := by
    change mixedMoment B node1661 node1661Labels = _
    exact sound1661 B hB hF
  have h2029 : mixedVector B (Sum.inr 2029) = Sparse.eval nodeValue2029 (mixedVector B) := by
    change mixedMoment B node2029 node2029Labels = _
    exact sound2029 B hB hF
  have h2066 : mixedVector B (Sum.inr 2066) = Sparse.eval nodeValue2066 (mixedVector B) := by
    change mixedMoment B node2066 node2066Labels = _
    exact sound2066 B hB hF
  have h2073 : mixedVector B (Sum.inr 2073) = Sparse.eval nodeValue2073 (mixedVector B) := by
    change mixedMoment B node2073 node2073Labels = _
    exact sound2073 B hB hF
  have h2082 : mixedVector B (Sum.inr 2082) = Sparse.eval nodeValue2082 (mixedVector B) := by
    change mixedMoment B node2082 node2082Labels = _
    exact sound2082 B hB hF
  have h2094 : mixedVector B (Sum.inr 2094) = Sparse.eval nodeValue2094 (mixedVector B) := by
    change mixedMoment B node2094 node2094Labels = _
    exact sound2094 B hB hF
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h2123 : mixedVector B (Sum.inr 2123) = Sparse.eval nodeValue2123 (mixedVector B) := by
    change mixedMoment B node2123 node2123Labels = _
    exact sound2123 B hB hF
  have h2138 : mixedVector B (Sum.inr 2138) = Sparse.eval nodeValue2138 (mixedVector B) := by
    change mixedMoment B node2138 node2138Labels = _
    exact sound2138 B hB hF
  have h2605 : mixedVector B (Sum.inr 2605) = Sparse.eval nodeValue2605 (mixedVector B) := by
    change mixedMoment B node2605 node2605Labels = _
    exact sound2605 B hB hF
  have h2621 : mixedVector B (Sum.inr 2621) = Sparse.eval nodeValue2621 (mixedVector B) := by
    change mixedMoment B node2621 node2621Labels = _
    exact sound2621 B hB hF
  have h2644 : mixedVector B (Sum.inr 2644) = Sparse.eval nodeValue2644 (mixedVector B) := by
    change mixedMoment B node2644 node2644Labels = _
    exact sound2644 B hB hF
  simpa only [sourceForm2269, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1641, h1653, h1661, h2029, h2066, h2073, h2082, h2094, h2115, h2123, h2138, h2605, h2621, h2644, reducedSource1856] using sourceEq2269 B hB

theorem rowSound1856 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1856 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1856, numericCheck1856, reducedZero1856 B hB hF, mul_zero]

theorem reducedZero1857 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1857 (mixedVector B) = 0 := by
  have h1876 : mixedVector B (Sum.inr 1876) = Sparse.eval nodeValue1876 (mixedVector B) := by
    change mixedMoment B node1876 node1876Labels = _
    exact sound1876 B hB hF
  have h1880 : mixedVector B (Sum.inr 1880) = Sparse.eval nodeValue1880 (mixedVector B) := by
    change mixedMoment B node1880 node1880Labels = _
    exact sound1880 B hB hF
  have h1881 : mixedVector B (Sum.inr 1881) = Sparse.eval nodeValue1881 (mixedVector B) := by
    change mixedMoment B node1881 node1881Labels = _
    exact sound1881 B hB hF
  have h1918 : mixedVector B (Sum.inr 1918) = Sparse.eval nodeValue1918 (mixedVector B) := by
    change mixedMoment B node1918 node1918Labels = _
    exact sound1918 B hB hF
  have h2082 : mixedVector B (Sum.inr 2082) = Sparse.eval nodeValue2082 (mixedVector B) := by
    change mixedMoment B node2082 node2082Labels = _
    exact sound2082 B hB hF
  have h3448 : mixedVector B (Sum.inr 3448) = Sparse.eval nodeValue3448 (mixedVector B) := by
    change mixedMoment B node3448 node3448Labels = _
    exact sound3448 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2271, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1876, h1880, h1881, h1918, h2082, h3448, h4080, reducedSource1857] using sourceEq2271 B hB

theorem rowSound1857 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1857 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1857, numericCheck1857, reducedZero1857 B hB hF, mul_zero]

theorem reducedZero1858 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1858 (mixedVector B) = 0 := by
  have h4328 : mixedVector B (Sum.inr 4328) = Sparse.eval nodeValue4328 (mixedVector B) := by
    change mixedMoment B node4328 node4328Labels = _
    exact sound4328 B hB hF
  have h4334 : mixedVector B (Sum.inr 4334) = Sparse.eval nodeValue4334 (mixedVector B) := by
    change mixedMoment B node4334 node4334Labels = _
    exact sound4334 B hB hF
  have h4336 : mixedVector B (Sum.inr 4336) = Sparse.eval nodeValue4336 (mixedVector B) := by
    change mixedMoment B node4336 node4336Labels = _
    exact sound4336 B hB hF
  have h4354 : mixedVector B (Sum.inr 4354) = Sparse.eval nodeValue4354 (mixedVector B) := by
    change mixedMoment B node4354 node4354Labels = _
    exact sound4354 B hB hF
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4665 : mixedVector B (Sum.inr 4665) = Sparse.eval nodeValue4665 (mixedVector B) := by
    change mixedMoment B node4665 node4665Labels = _
    exact sound4665 B hB hF
  have h4667 : mixedVector B (Sum.inr 4667) = Sparse.eval nodeValue4667 (mixedVector B) := by
    change mixedMoment B node4667 node4667Labels = _
    exact sound4667 B hB hF
  have h4669 : mixedVector B (Sum.inr 4669) = Sparse.eval nodeValue4669 (mixedVector B) := by
    change mixedMoment B node4669 node4669Labels = _
    exact sound4669 B hB hF
  have h4671 : mixedVector B (Sum.inr 4671) = Sparse.eval nodeValue4671 (mixedVector B) := by
    change mixedMoment B node4671 node4671Labels = _
    exact sound4671 B hB hF
  have h4687 : mixedVector B (Sum.inr 4687) = Sparse.eval nodeValue4687 (mixedVector B) := by
    change mixedMoment B node4687 node4687Labels = _
    exact sound4687 B hB hF
  have h4688 : mixedVector B (Sum.inr 4688) = Sparse.eval nodeValue4688 (mixedVector B) := by
    change mixedMoment B node4688 node4688Labels = _
    exact sound4688 B hB hF
  have h4756 : mixedVector B (Sum.inr 4756) = Sparse.eval nodeValue4756 (mixedVector B) := by
    change mixedMoment B node4756 node4756Labels = _
    exact sound4756 B hB hF
  have h4766 : mixedVector B (Sum.inr 4766) = Sparse.eval nodeValue4766 (mixedVector B) := by
    change mixedMoment B node4766 node4766Labels = _
    exact sound4766 B hB hF
  have h4773 : mixedVector B (Sum.inr 4773) = Sparse.eval nodeValue4773 (mixedVector B) := by
    change mixedMoment B node4773 node4773Labels = _
    exact sound4773 B hB hF
  have h4776 : mixedVector B (Sum.inr 4776) = Sparse.eval nodeValue4776 (mixedVector B) := by
    change mixedMoment B node4776 node4776Labels = _
    exact sound4776 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h4803 : mixedVector B (Sum.inr 4803) = Sparse.eval nodeValue4803 (mixedVector B) := by
    change mixedMoment B node4803 node4803Labels = _
    exact sound4803 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4808 : mixedVector B (Sum.inr 4808) = Sparse.eval nodeValue4808 (mixedVector B) := by
    change mixedMoment B node4808 node4808Labels = _
    exact sound4808 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4874 : mixedVector B (Sum.inr 4874) = Sparse.eval nodeValue4874 (mixedVector B) := by
    change mixedMoment B node4874 node4874Labels = _
    exact sound4874 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h5232 : mixedVector B (Sum.inr 5232) = Sparse.eval nodeValue5232 (mixedVector B) := by
    change mixedMoment B node5232 node5232Labels = _
    exact sound5232 B hB hF
  have h5243 : mixedVector B (Sum.inr 5243) = Sparse.eval nodeValue5243 (mixedVector B) := by
    change mixedMoment B node5243 node5243Labels = _
    exact sound5243 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5264 : mixedVector B (Sum.inr 5264) = Sparse.eval nodeValue5264 (mixedVector B) := by
    change mixedMoment B node5264 node5264Labels = _
    exact sound5264 B hB hF
  have h5266 : mixedVector B (Sum.inr 5266) = Sparse.eval nodeValue5266 (mixedVector B) := by
    change mixedMoment B node5266 node5266Labels = _
    exact sound5266 B hB hF
  simpa only [sourceForm2273, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4328, h4334, h4336, h4354, h4466, h4665, h4667, h4669, h4671, h4687, h4688, h4756, h4766, h4773, h4776, h4801, h4803, h4804, h4808, h4810, h4834, h4839, h4874, h4894, h4896, h5232, h5243, h5258, h5264, h5266, reducedSource1858] using sourceEq2273 B hB

theorem rowSound1858 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1858 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1858, numericCheck1858, reducedZero1858 B hB hF, mul_zero]

theorem reducedZero1859 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1859 (mixedVector B) = 0 := by
  have h1330 : mixedVector B (Sum.inr 1330) = Sparse.eval nodeValue1330 (mixedVector B) := by
    change mixedMoment B node1330 node1330Labels = _
    exact sound1330 B hB hF
  have h1332 : mixedVector B (Sum.inr 1332) = Sparse.eval nodeValue1332 (mixedVector B) := by
    change mixedMoment B node1332 node1332Labels = _
    exact sound1332 B hB hF
  have h1334 : mixedVector B (Sum.inr 1334) = Sparse.eval nodeValue1334 (mixedVector B) := by
    change mixedMoment B node1334 node1334Labels = _
    exact sound1334 B hB hF
  have h1343 : mixedVector B (Sum.inr 1343) = Sparse.eval nodeValue1343 (mixedVector B) := by
    change mixedMoment B node1343 node1343Labels = _
    exact sound1343 B hB hF
  have h1419 : mixedVector B (Sum.inr 1419) = Sparse.eval nodeValue1419 (mixedVector B) := by
    change mixedMoment B node1419 node1419Labels = _
    exact sound1419 B hB hF
  have h1793 : mixedVector B (Sum.inr 1793) = Sparse.eval nodeValue1793 (mixedVector B) := by
    change mixedMoment B node1793 node1793Labels = _
    exact sound1793 B hB hF
  have h1797 : mixedVector B (Sum.inr 1797) = Sparse.eval nodeValue1797 (mixedVector B) := by
    change mixedMoment B node1797 node1797Labels = _
    exact sound1797 B hB hF
  have h1813 : mixedVector B (Sum.inr 1813) = Sparse.eval nodeValue1813 (mixedVector B) := by
    change mixedMoment B node1813 node1813Labels = _
    exact sound1813 B hB hF
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2800 : mixedVector B (Sum.inr 2800) = Sparse.eval nodeValue2800 (mixedVector B) := by
    change mixedMoment B node2800 node2800Labels = _
    exact sound2800 B hB hF
  have h2803 : mixedVector B (Sum.inr 2803) = Sparse.eval nodeValue2803 (mixedVector B) := by
    change mixedMoment B node2803 node2803Labels = _
    exact sound2803 B hB hF
  have h2816 : mixedVector B (Sum.inr 2816) = Sparse.eval nodeValue2816 (mixedVector B) := by
    change mixedMoment B node2816 node2816Labels = _
    exact sound2816 B hB hF
  have h2941 : mixedVector B (Sum.inr 2941) = Sparse.eval nodeValue2941 (mixedVector B) := by
    change mixedMoment B node2941 node2941Labels = _
    exact sound2941 B hB hF
  have h3030 : mixedVector B (Sum.inr 3030) = Sparse.eval nodeValue3030 (mixedVector B) := by
    change mixedMoment B node3030 node3030Labels = _
    exact sound3030 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3040 : mixedVector B (Sum.inr 3040) = Sparse.eval nodeValue3040 (mixedVector B) := by
    change mixedMoment B node3040 node3040Labels = _
    exact sound3040 B hB hF
  have h3045 : mixedVector B (Sum.inr 3045) = Sparse.eval nodeValue3045 (mixedVector B) := by
    change mixedMoment B node3045 node3045Labels = _
    exact sound3045 B hB hF
  have h3089 : mixedVector B (Sum.inr 3089) = Sparse.eval nodeValue3089 (mixedVector B) := by
    change mixedMoment B node3089 node3089Labels = _
    exact sound3089 B hB hF
  have h3134 : mixedVector B (Sum.inr 3134) = Sparse.eval nodeValue3134 (mixedVector B) := by
    change mixedMoment B node3134 node3134Labels = _
    exact sound3134 B hB hF
  have h3141 : mixedVector B (Sum.inr 3141) = Sparse.eval nodeValue3141 (mixedVector B) := by
    change mixedMoment B node3141 node3141Labels = _
    exact sound3141 B hB hF
  have h3163 : mixedVector B (Sum.inr 3163) = Sparse.eval nodeValue3163 (mixedVector B) := by
    change mixedMoment B node3163 node3163Labels = _
    exact sound3163 B hB hF
  have h3187 : mixedVector B (Sum.inr 3187) = Sparse.eval nodeValue3187 (mixedVector B) := by
    change mixedMoment B node3187 node3187Labels = _
    exact sound3187 B hB hF
  have h3190 : mixedVector B (Sum.inr 3190) = Sparse.eval nodeValue3190 (mixedVector B) := by
    change mixedMoment B node3190 node3190Labels = _
    exact sound3190 B hB hF
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3205 : mixedVector B (Sum.inr 3205) = Sparse.eval nodeValue3205 (mixedVector B) := by
    change mixedMoment B node3205 node3205Labels = _
    exact sound3205 B hB hF
  have h3206 : mixedVector B (Sum.inr 3206) = Sparse.eval nodeValue3206 (mixedVector B) := by
    change mixedMoment B node3206 node3206Labels = _
    exact sound3206 B hB hF
  have h3210 : mixedVector B (Sum.inr 3210) = Sparse.eval nodeValue3210 (mixedVector B) := by
    change mixedMoment B node3210 node3210Labels = _
    exact sound3210 B hB hF
  have h3214 : mixedVector B (Sum.inr 3214) = Sparse.eval nodeValue3214 (mixedVector B) := by
    change mixedMoment B node3214 node3214Labels = _
    exact sound3214 B hB hF
  have h3225 : mixedVector B (Sum.inr 3225) = Sparse.eval nodeValue3225 (mixedVector B) := by
    change mixedMoment B node3225 node3225Labels = _
    exact sound3225 B hB hF
  have h3230 : mixedVector B (Sum.inr 3230) = Sparse.eval nodeValue3230 (mixedVector B) := by
    change mixedMoment B node3230 node3230Labels = _
    exact sound3230 B hB hF
  simpa only [sourceForm2274, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1330, h1332, h1334, h1343, h1419, h1793, h1797, h1813, h2092, h2800, h2803, h2816, h2941, h3030, h3039, h3040, h3045, h3089, h3134, h3141, h3163, h3187, h3190, h3202, h3205, h3206, h3210, h3214, h3225, h3230, reducedSource1859] using sourceEq2274 B hB

theorem rowSound1859 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1859 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1859, numericCheck1859, reducedZero1859 B hB hF, mul_zero]

theorem reducedZero1860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1860 (mixedVector B) = 0 := by
  have h1667 : mixedVector B (Sum.inr 1667) = Sparse.eval nodeValue1667 (mixedVector B) := by
    change mixedMoment B node1667 node1667Labels = _
    exact sound1667 B hB hF
  have h1679 : mixedVector B (Sum.inr 1679) = Sparse.eval nodeValue1679 (mixedVector B) := by
    change mixedMoment B node1679 node1679Labels = _
    exact sound1679 B hB hF
  have h1681 : mixedVector B (Sum.inr 1681) = Sparse.eval nodeValue1681 (mixedVector B) := by
    change mixedMoment B node1681 node1681Labels = _
    exact sound1681 B hB hF
  have h1685 : mixedVector B (Sum.inr 1685) = Sparse.eval nodeValue1685 (mixedVector B) := by
    change mixedMoment B node1685 node1685Labels = _
    exact sound1685 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h2144 : mixedVector B (Sum.inr 2144) = Sparse.eval nodeValue2144 (mixedVector B) := by
    change mixedMoment B node2144 node2144Labels = _
    exact sound2144 B hB hF
  have h2155 : mixedVector B (Sum.inr 2155) = Sparse.eval nodeValue2155 (mixedVector B) := by
    change mixedMoment B node2155 node2155Labels = _
    exact sound2155 B hB hF
  have h2157 : mixedVector B (Sum.inr 2157) = Sparse.eval nodeValue2157 (mixedVector B) := by
    change mixedMoment B node2157 node2157Labels = _
    exact sound2157 B hB hF
  have h2160 : mixedVector B (Sum.inr 2160) = Sparse.eval nodeValue2160 (mixedVector B) := by
    change mixedMoment B node2160 node2160Labels = _
    exact sound2160 B hB hF
  have h2161 : mixedVector B (Sum.inr 2161) = Sparse.eval nodeValue2161 (mixedVector B) := by
    change mixedMoment B node2161 node2161Labels = _
    exact sound2161 B hB hF
  have h2162 : mixedVector B (Sum.inr 2162) = Sparse.eval nodeValue2162 (mixedVector B) := by
    change mixedMoment B node2162 node2162Labels = _
    exact sound2162 B hB hF
  have h2176 : mixedVector B (Sum.inr 2176) = Sparse.eval nodeValue2176 (mixedVector B) := by
    change mixedMoment B node2176 node2176Labels = _
    exact sound2176 B hB hF
  have h2177 : mixedVector B (Sum.inr 2177) = Sparse.eval nodeValue2177 (mixedVector B) := by
    change mixedMoment B node2177 node2177Labels = _
    exact sound2177 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2194 : mixedVector B (Sum.inr 2194) = Sparse.eval nodeValue2194 (mixedVector B) := by
    change mixedMoment B node2194 node2194Labels = _
    exact sound2194 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2212 : mixedVector B (Sum.inr 2212) = Sparse.eval nodeValue2212 (mixedVector B) := by
    change mixedMoment B node2212 node2212Labels = _
    exact sound2212 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2677 : mixedVector B (Sum.inr 2677) = Sparse.eval nodeValue2677 (mixedVector B) := by
    change mixedMoment B node2677 node2677Labels = _
    exact sound2677 B hB hF
  have h2697 : mixedVector B (Sum.inr 2697) = Sparse.eval nodeValue2697 (mixedVector B) := by
    change mixedMoment B node2697 node2697Labels = _
    exact sound2697 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2729 : mixedVector B (Sum.inr 2729) = Sparse.eval nodeValue2729 (mixedVector B) := by
    change mixedMoment B node2729 node2729Labels = _
    exact sound2729 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  simpa only [sourceForm2275, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1667, h1679, h1681, h1685, h1738, h2144, h2155, h2157, h2160, h2161, h2162, h2176, h2177, h2190, h2194, h2195, h2203, h2205, h2212, h2215, h2216, h2220, h2264, h2276, h2278, h2677, h2697, h2722, h2729, h2731, reducedSource1860] using sourceEq2275 B hB

theorem rowSound1860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1860 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1860, numericCheck1860, reducedZero1860 B hB hF, mul_zero]

theorem reducedZero1861 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1861 (mixedVector B) = 0 := by
  have h1791 : mixedVector B (Sum.inr 1791) = Sparse.eval nodeValue1791 (mixedVector B) := by
    change mixedMoment B node1791 node1791Labels = _
    exact sound1791 B hB hF
  have h1795 : mixedVector B (Sum.inr 1795) = Sparse.eval nodeValue1795 (mixedVector B) := by
    change mixedMoment B node1795 node1795Labels = _
    exact sound1795 B hB hF
  have h1797 : mixedVector B (Sum.inr 1797) = Sparse.eval nodeValue1797 (mixedVector B) := by
    change mixedMoment B node1797 node1797Labels = _
    exact sound1797 B hB hF
  have h1814 : mixedVector B (Sum.inr 1814) = Sparse.eval nodeValue1814 (mixedVector B) := by
    change mixedMoment B node1814 node1814Labels = _
    exact sound1814 B hB hF
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h3379 : mixedVector B (Sum.inr 3379) = Sparse.eval nodeValue3379 (mixedVector B) := by
    change mixedMoment B node3379 node3379Labels = _
    exact sound3379 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2276, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1791, h1795, h1797, h1814, h2028, h3379, h4084, reducedSource1861] using sourceEq2276 B hB

theorem rowSound1861 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1861 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1861, numericCheck1861, reducedZero1861 B hB hF, mul_zero]

theorem reducedZero1862 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1862 (mixedVector B) = 0 := by
  have h932 : mixedVector B (Sum.inr 932) = Sparse.eval nodeValue932 (mixedVector B) := by
    change mixedMoment B node932 node932Labels = _
    exact sound932 B hB hF
  have h1814 : mixedVector B (Sum.inr 1814) = Sparse.eval nodeValue1814 (mixedVector B) := by
    change mixedMoment B node1814 node1814Labels = _
    exact sound1814 B hB hF
  have h1966 : mixedVector B (Sum.inr 1966) = Sparse.eval nodeValue1966 (mixedVector B) := by
    change mixedMoment B node1966 node1966Labels = _
    exact sound1966 B hB hF
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h2053 : mixedVector B (Sum.inr 2053) = Sparse.eval nodeValue2053 (mixedVector B) := by
    change mixedMoment B node2053 node2053Labels = _
    exact sound2053 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2277, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h932, h1814, h1966, h2028, h2053, h2058, h4084, reducedSource1862] using sourceEq2277 B hB

theorem rowSound1862 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1862 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1862, numericCheck1862, reducedZero1862 B hB hF, mul_zero]

theorem reducedZero1863 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1863 (mixedVector B) = 0 := by
  have h906 : mixedVector B (Sum.inr 906) = Sparse.eval nodeValue906 (mixedVector B) := by
    change mixedMoment B node906 node906Labels = _
    exact sound906 B hB hF
  have h1791 : mixedVector B (Sum.inr 1791) = Sparse.eval nodeValue1791 (mixedVector B) := by
    change mixedMoment B node1791 node1791Labels = _
    exact sound1791 B hB hF
  have h1974 : mixedVector B (Sum.inr 1974) = Sparse.eval nodeValue1974 (mixedVector B) := by
    change mixedMoment B node1974 node1974Labels = _
    exact sound1974 B hB hF
  have h2019 : mixedVector B (Sum.inr 2019) = Sparse.eval nodeValue2019 (mixedVector B) := by
    change mixedMoment B node2019 node2019Labels = _
    exact sound2019 B hB hF
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2278, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h906, h1791, h1974, h2019, h2021, h2028, h4084, reducedSource1863] using sourceEq2278 B hB

theorem rowSound1863 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1863 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1863, numericCheck1863, reducedZero1863 B hB hF, mul_zero]

theorem reducedZero1864 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1864 (mixedVector B) = 0 := by
  have h4200 : mixedVector B (Sum.inr 4200) = Sparse.eval nodeValue4200 (mixedVector B) := by
    change mixedMoment B node4200 node4200Labels = _
    exact sound4200 B hB hF
  have h4203 : mixedVector B (Sum.inr 4203) = Sparse.eval nodeValue4203 (mixedVector B) := by
    change mixedMoment B node4203 node4203Labels = _
    exact sound4203 B hB hF
  have h4205 : mixedVector B (Sum.inr 4205) = Sparse.eval nodeValue4205 (mixedVector B) := by
    change mixedMoment B node4205 node4205Labels = _
    exact sound4205 B hB hF
  have h4223 : mixedVector B (Sum.inr 4223) = Sparse.eval nodeValue4223 (mixedVector B) := by
    change mixedMoment B node4223 node4223Labels = _
    exact sound4223 B hB hF
  have h4255 : mixedVector B (Sum.inr 4255) = Sparse.eval nodeValue4255 (mixedVector B) := by
    change mixedMoment B node4255 node4255Labels = _
    exact sound4255 B hB hF
  have h4634 : mixedVector B (Sum.inr 4634) = Sparse.eval nodeValue4634 (mixedVector B) := by
    change mixedMoment B node4634 node4634Labels = _
    exact sound4634 B hB hF
  have h4636 : mixedVector B (Sum.inr 4636) = Sparse.eval nodeValue4636 (mixedVector B) := by
    change mixedMoment B node4636 node4636Labels = _
    exact sound4636 B hB hF
  have h4638 : mixedVector B (Sum.inr 4638) = Sparse.eval nodeValue4638 (mixedVector B) := by
    change mixedMoment B node4638 node4638Labels = _
    exact sound4638 B hB hF
  have h4653 : mixedVector B (Sum.inr 4653) = Sparse.eval nodeValue4653 (mixedVector B) := by
    change mixedMoment B node4653 node4653Labels = _
    exact sound4653 B hB hF
  have h4658 : mixedVector B (Sum.inr 4658) = Sparse.eval nodeValue4658 (mixedVector B) := by
    change mixedMoment B node4658 node4658Labels = _
    exact sound4658 B hB hF
  have h4678 : mixedVector B (Sum.inr 4678) = Sparse.eval nodeValue4678 (mixedVector B) := by
    change mixedMoment B node4678 node4678Labels = _
    exact sound4678 B hB hF
  have h4707 : mixedVector B (Sum.inr 4707) = Sparse.eval nodeValue4707 (mixedVector B) := by
    change mixedMoment B node4707 node4707Labels = _
    exact sound4707 B hB hF
  have h4716 : mixedVector B (Sum.inr 4716) = Sparse.eval nodeValue4716 (mixedVector B) := by
    change mixedMoment B node4716 node4716Labels = _
    exact sound4716 B hB hF
  have h4731 : mixedVector B (Sum.inr 4731) = Sparse.eval nodeValue4731 (mixedVector B) := by
    change mixedMoment B node4731 node4731Labels = _
    exact sound4731 B hB hF
  have h4766 : mixedVector B (Sum.inr 4766) = Sparse.eval nodeValue4766 (mixedVector B) := by
    change mixedMoment B node4766 node4766Labels = _
    exact sound4766 B hB hF
  have h4770 : mixedVector B (Sum.inr 4770) = Sparse.eval nodeValue4770 (mixedVector B) := by
    change mixedMoment B node4770 node4770Labels = _
    exact sound4770 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4800 : mixedVector B (Sum.inr 4800) = Sparse.eval nodeValue4800 (mixedVector B) := by
    change mixedMoment B node4800 node4800Labels = _
    exact sound4800 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4828 : mixedVector B (Sum.inr 4828) = Sparse.eval nodeValue4828 (mixedVector B) := by
    change mixedMoment B node4828 node4828Labels = _
    exact sound4828 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387 B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435 B hB hF
  simpa only [sourceForm2279, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4200, h4203, h4205, h4223, h4255, h4634, h4636, h4638, h4653, h4658, h4678, h4707, h4716, h4731, h4766, h4770, h4798, h4800, h4805, h4807, h4810, h4828, h4839, h4865, h4889, h5355, h5378, h5387, h5432, h5435, reducedSource1864] using sourceEq2279 B hB

theorem rowSound1864 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1864 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1864, numericCheck1864, reducedZero1864 B hB hF, mul_zero]

theorem reducedZero1865 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1865 (mixedVector B) = 0 := by
  have h4329 : mixedVector B (Sum.inr 4329) = Sparse.eval nodeValue4329 (mixedVector B) := by
    change mixedMoment B node4329 node4329Labels = _
    exact sound4329 B hB hF
  have h4335 : mixedVector B (Sum.inr 4335) = Sparse.eval nodeValue4335 (mixedVector B) := by
    change mixedMoment B node4335 node4335Labels = _
    exact sound4335 B hB hF
  have h4355 : mixedVector B (Sum.inr 4355) = Sparse.eval nodeValue4355 (mixedVector B) := by
    change mixedMoment B node4355 node4355Labels = _
    exact sound4355 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4666 : mixedVector B (Sum.inr 4666) = Sparse.eval nodeValue4666 (mixedVector B) := by
    change mixedMoment B node4666 node4666Labels = _
    exact sound4666 B hB hF
  have h4670 : mixedVector B (Sum.inr 4670) = Sparse.eval nodeValue4670 (mixedVector B) := by
    change mixedMoment B node4670 node4670Labels = _
    exact sound4670 B hB hF
  have h4689 : mixedVector B (Sum.inr 4689) = Sparse.eval nodeValue4689 (mixedVector B) := by
    change mixedMoment B node4689 node4689Labels = _
    exact sound4689 B hB hF
  have h4757 : mixedVector B (Sum.inr 4757) = Sparse.eval nodeValue4757 (mixedVector B) := by
    change mixedMoment B node4757 node4757Labels = _
    exact sound4757 B hB hF
  have h4767 : mixedVector B (Sum.inr 4767) = Sparse.eval nodeValue4767 (mixedVector B) := by
    change mixedMoment B node4767 node4767Labels = _
    exact sound4767 B hB hF
  have h4774 : mixedVector B (Sum.inr 4774) = Sparse.eval nodeValue4774 (mixedVector B) := by
    change mixedMoment B node4774 node4774Labels = _
    exact sound4774 B hB hF
  have h4777 : mixedVector B (Sum.inr 4777) = Sparse.eval nodeValue4777 (mixedVector B) := by
    change mixedMoment B node4777 node4777Labels = _
    exact sound4777 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4875 : mixedVector B (Sum.inr 4875) = Sparse.eval nodeValue4875 (mixedVector B) := by
    change mixedMoment B node4875 node4875Labels = _
    exact sound4875 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h5236 : mixedVector B (Sum.inr 5236) = Sparse.eval nodeValue5236 (mixedVector B) := by
    change mixedMoment B node5236 node5236Labels = _
    exact sound5236 B hB hF
  have h5246 : mixedVector B (Sum.inr 5246) = Sparse.eval nodeValue5246 (mixedVector B) := by
    change mixedMoment B node5246 node5246Labels = _
    exact sound5246 B hB hF
  have h5269 : mixedVector B (Sum.inr 5269) = Sparse.eval nodeValue5269 (mixedVector B) := by
    change mixedMoment B node5269 node5269Labels = _
    exact sound5269 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  simpa only [sourceForm2283, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4329, h4335, h4355, h4467, h4666, h4670, h4689, h4757, h4767, h4774, h4777, h4802, h4807, h4811, h4838, h4875, h4895, h5236, h5246, h5269, h5271, reducedSource1865] using sourceEq2283 B hB

theorem rowSound1865 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1865 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1865, numericCheck1865, reducedZero1865 B hB hF, mul_zero]

theorem reducedZero1866 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1866 (mixedVector B) = 0 := by
  have h1331 : mixedVector B (Sum.inr 1331) = Sparse.eval nodeValue1331 (mixedVector B) := by
    change mixedMoment B node1331 node1331Labels = _
    exact sound1331 B hB hF
  have h1333 : mixedVector B (Sum.inr 1333) = Sparse.eval nodeValue1333 (mixedVector B) := by
    change mixedMoment B node1333 node1333Labels = _
    exact sound1333 B hB hF
  have h1344 : mixedVector B (Sum.inr 1344) = Sparse.eval nodeValue1344 (mixedVector B) := by
    change mixedMoment B node1344 node1344Labels = _
    exact sound1344 B hB hF
  have h1420 : mixedVector B (Sum.inr 1420) = Sparse.eval nodeValue1420 (mixedVector B) := by
    change mixedMoment B node1420 node1420Labels = _
    exact sound1420 B hB hF
  have h2323 : mixedVector B (Sum.inr 2323) = Sparse.eval nodeValue2323 (mixedVector B) := by
    change mixedMoment B node2323 node2323Labels = _
    exact sound2323 B hB hF
  have h2327 : mixedVector B (Sum.inr 2327) = Sparse.eval nodeValue2327 (mixedVector B) := by
    change mixedMoment B node2327 node2327Labels = _
    exact sound2327 B hB hF
  have h2340 : mixedVector B (Sum.inr 2340) = Sparse.eval nodeValue2340 (mixedVector B) := by
    change mixedMoment B node2340 node2340Labels = _
    exact sound2340 B hB hF
  have h2574 : mixedVector B (Sum.inr 2574) = Sparse.eval nodeValue2574 (mixedVector B) := by
    change mixedMoment B node2574 node2574Labels = _
    exact sound2574 B hB hF
  have h3104 : mixedVector B (Sum.inr 3104) = Sparse.eval nodeValue3104 (mixedVector B) := by
    change mixedMoment B node3104 node3104Labels = _
    exact sound3104 B hB hF
  have h3108 : mixedVector B (Sum.inr 3108) = Sparse.eval nodeValue3108 (mixedVector B) := by
    change mixedMoment B node3108 node3108Labels = _
    exact sound3108 B hB hF
  have h3109 : mixedVector B (Sum.inr 3109) = Sparse.eval nodeValue3109 (mixedVector B) := by
    change mixedMoment B node3109 node3109Labels = _
    exact sound3109 B hB hF
  have h3115 : mixedVector B (Sum.inr 3115) = Sparse.eval nodeValue3115 (mixedVector B) := by
    change mixedMoment B node3115 node3115Labels = _
    exact sound3115 B hB hF
  have h3135 : mixedVector B (Sum.inr 3135) = Sparse.eval nodeValue3135 (mixedVector B) := by
    change mixedMoment B node3135 node3135Labels = _
    exact sound3135 B hB hF
  have h3142 : mixedVector B (Sum.inr 3142) = Sparse.eval nodeValue3142 (mixedVector B) := by
    change mixedMoment B node3142 node3142Labels = _
    exact sound3142 B hB hF
  have h3164 : mixedVector B (Sum.inr 3164) = Sparse.eval nodeValue3164 (mixedVector B) := by
    change mixedMoment B node3164 node3164Labels = _
    exact sound3164 B hB hF
  have h3188 : mixedVector B (Sum.inr 3188) = Sparse.eval nodeValue3188 (mixedVector B) := by
    change mixedMoment B node3188 node3188Labels = _
    exact sound3188 B hB hF
  have h3191 : mixedVector B (Sum.inr 3191) = Sparse.eval nodeValue3191 (mixedVector B) := by
    change mixedMoment B node3191 node3191Labels = _
    exact sound3191 B hB hF
  have h3204 : mixedVector B (Sum.inr 3204) = Sparse.eval nodeValue3204 (mixedVector B) := by
    change mixedMoment B node3204 node3204Labels = _
    exact sound3204 B hB hF
  have h3207 : mixedVector B (Sum.inr 3207) = Sparse.eval nodeValue3207 (mixedVector B) := by
    change mixedMoment B node3207 node3207Labels = _
    exact sound3207 B hB hF
  have h3213 : mixedVector B (Sum.inr 3213) = Sparse.eval nodeValue3213 (mixedVector B) := by
    change mixedMoment B node3213 node3213Labels = _
    exact sound3213 B hB hF
  have h3229 : mixedVector B (Sum.inr 3229) = Sparse.eval nodeValue3229 (mixedVector B) := by
    change mixedMoment B node3229 node3229Labels = _
    exact sound3229 B hB hF
  simpa only [sourceForm2284, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1331, h1333, h1344, h1420, h2323, h2327, h2340, h2574, h3104, h3108, h3109, h3115, h3135, h3142, h3164, h3188, h3191, h3204, h3207, h3213, h3229, reducedSource1866] using sourceEq2284 B hB

theorem rowSound1866 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1866 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1866, numericCheck1866, reducedZero1866 B hB hF, mul_zero]

theorem reducedZero1867 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1867 (mixedVector B) = 0 := by
  have h1671 : mixedVector B (Sum.inr 1671) = Sparse.eval nodeValue1671 (mixedVector B) := by
    change mixedMoment B node1671 node1671Labels = _
    exact sound1671 B hB hF
  have h1689 : mixedVector B (Sum.inr 1689) = Sparse.eval nodeValue1689 (mixedVector B) := by
    change mixedMoment B node1689 node1689Labels = _
    exact sound1689 B hB hF
  have h1691 : mixedVector B (Sum.inr 1691) = Sparse.eval nodeValue1691 (mixedVector B) := by
    change mixedMoment B node1691 node1691Labels = _
    exact sound1691 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h2148 : mixedVector B (Sum.inr 2148) = Sparse.eval nodeValue2148 (mixedVector B) := by
    change mixedMoment B node2148 node2148Labels = _
    exact sound2148 B hB hF
  have h2164 : mixedVector B (Sum.inr 2164) = Sparse.eval nodeValue2164 (mixedVector B) := by
    change mixedMoment B node2164 node2164Labels = _
    exact sound2164 B hB hF
  have h2166 : mixedVector B (Sum.inr 2166) = Sparse.eval nodeValue2166 (mixedVector B) := by
    change mixedMoment B node2166 node2166Labels = _
    exact sound2166 B hB hF
  have h2181 : mixedVector B (Sum.inr 2181) = Sparse.eval nodeValue2181 (mixedVector B) := by
    change mixedMoment B node2181 node2181Labels = _
    exact sound2181 B hB hF
  have h2183 : mixedVector B (Sum.inr 2183) = Sparse.eval nodeValue2183 (mixedVector B) := by
    change mixedMoment B node2183 node2183Labels = _
    exact sound2183 B hB hF
  have h2199 : mixedVector B (Sum.inr 2199) = Sparse.eval nodeValue2199 (mixedVector B) := by
    change mixedMoment B node2199 node2199Labels = _
    exact sound2199 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2223 : mixedVector B (Sum.inr 2223) = Sparse.eval nodeValue2223 (mixedVector B) := by
    change mixedMoment B node2223 node2223Labels = _
    exact sound2223 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2227 : mixedVector B (Sum.inr 2227) = Sparse.eval nodeValue2227 (mixedVector B) := by
    change mixedMoment B node2227 node2227Labels = _
    exact sound2227 B hB hF
  have h2288 : mixedVector B (Sum.inr 2288) = Sparse.eval nodeValue2288 (mixedVector B) := by
    change mixedMoment B node2288 node2288Labels = _
    exact sound2288 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h2682 : mixedVector B (Sum.inr 2682) = Sparse.eval nodeValue2682 (mixedVector B) := by
    change mixedMoment B node2682 node2682Labels = _
    exact sound2682 B hB hF
  have h2701 : mixedVector B (Sum.inr 2701) = Sparse.eval nodeValue2701 (mixedVector B) := by
    change mixedMoment B node2701 node2701Labels = _
    exact sound2701 B hB hF
  have h2736 : mixedVector B (Sum.inr 2736) = Sparse.eval nodeValue2736 (mixedVector B) := by
    change mixedMoment B node2736 node2736Labels = _
    exact sound2736 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  simpa only [sourceForm2285, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1671, h1689, h1691, h1751, h2148, h2164, h2166, h2181, h2183, h2199, h2202, h2223, h2224, h2225, h2227, h2288, h2291, h2682, h2701, h2736, h2739, reducedSource1867] using sourceEq2285 B hB

theorem rowSound1867 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1867 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1867, numericCheck1867, reducedZero1867 B hB hF, mul_zero]

theorem reducedZero1868 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1868 (mixedVector B) = 0 := by
  have h1792 : mixedVector B (Sum.inr 1792) = Sparse.eval nodeValue1792 (mixedVector B) := by
    change mixedMoment B node1792 node1792Labels = _
    exact sound1792 B hB hF
  have h1796 : mixedVector B (Sum.inr 1796) = Sparse.eval nodeValue1796 (mixedVector B) := by
    change mixedMoment B node1796 node1796Labels = _
    exact sound1796 B hB hF
  have h1815 : mixedVector B (Sum.inr 1815) = Sparse.eval nodeValue1815 (mixedVector B) := by
    change mixedMoment B node1815 node1815Labels = _
    exact sound1815 B hB hF
  have h2029 : mixedVector B (Sum.inr 2029) = Sparse.eval nodeValue2029 (mixedVector B) := by
    change mixedMoment B node2029 node2029Labels = _
    exact sound2029 B hB hF
  have h3380 : mixedVector B (Sum.inr 3380) = Sparse.eval nodeValue3380 (mixedVector B) := by
    change mixedMoment B node3380 node3380Labels = _
    exact sound3380 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2286, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1792, h1796, h1815, h2029, h3380, h4083, reducedSource1868] using sourceEq2286 B hB

theorem rowSound1868 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1868 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1868, numericCheck1868, reducedZero1868 B hB hF, mul_zero]

theorem reducedZero1869 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1869 (mixedVector B) = 0 := by
  have h933 : mixedVector B (Sum.inr 933) = Sparse.eval nodeValue933 (mixedVector B) := by
    change mixedMoment B node933 node933Labels = _
    exact sound933 B hB hF
  have h1815 : mixedVector B (Sum.inr 1815) = Sparse.eval nodeValue1815 (mixedVector B) := by
    change mixedMoment B node1815 node1815Labels = _
    exact sound1815 B hB hF
  have h1967 : mixedVector B (Sum.inr 1967) = Sparse.eval nodeValue1967 (mixedVector B) := by
    change mixedMoment B node1967 node1967Labels = _
    exact sound1967 B hB hF
  have h2029 : mixedVector B (Sum.inr 2029) = Sparse.eval nodeValue2029 (mixedVector B) := by
    change mixedMoment B node2029 node2029Labels = _
    exact sound2029 B hB hF
  have h2057 : mixedVector B (Sum.inr 2057) = Sparse.eval nodeValue2057 (mixedVector B) := by
    change mixedMoment B node2057 node2057Labels = _
    exact sound2057 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2287, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h933, h1815, h1967, h2029, h2057, h4083, reducedSource1869] using sourceEq2287 B hB

theorem rowSound1869 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1869 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1869, numericCheck1869, reducedZero1869 B hB hF, mul_zero]

theorem reducedZero1870 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1870 (mixedVector B) = 0 := by
  have h907 : mixedVector B (Sum.inr 907) = Sparse.eval nodeValue907 (mixedVector B) := by
    change mixedMoment B node907 node907Labels = _
    exact sound907 B hB hF
  have h1792 : mixedVector B (Sum.inr 1792) = Sparse.eval nodeValue1792 (mixedVector B) := by
    change mixedMoment B node1792 node1792Labels = _
    exact sound1792 B hB hF
  have h1975 : mixedVector B (Sum.inr 1975) = Sparse.eval nodeValue1975 (mixedVector B) := by
    change mixedMoment B node1975 node1975Labels = _
    exact sound1975 B hB hF
  have h2020 : mixedVector B (Sum.inr 2020) = Sparse.eval nodeValue2020 (mixedVector B) := by
    change mixedMoment B node2020 node2020Labels = _
    exact sound2020 B hB hF
  have h2029 : mixedVector B (Sum.inr 2029) = Sparse.eval nodeValue2029 (mixedVector B) := by
    change mixedMoment B node2029 node2029Labels = _
    exact sound2029 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2288, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h907, h1792, h1975, h2020, h2029, h4083, reducedSource1870] using sourceEq2288 B hB

theorem rowSound1870 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1870 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1870, numericCheck1870, reducedZero1870 B hB hF, mul_zero]

theorem reducedZero1871 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1871 (mixedVector B) = 0 := by
  have h4201 : mixedVector B (Sum.inr 4201) = Sparse.eval nodeValue4201 (mixedVector B) := by
    change mixedMoment B node4201 node4201Labels = _
    exact sound4201 B hB hF
  have h4204 : mixedVector B (Sum.inr 4204) = Sparse.eval nodeValue4204 (mixedVector B) := by
    change mixedMoment B node4204 node4204Labels = _
    exact sound4204 B hB hF
  have h4224 : mixedVector B (Sum.inr 4224) = Sparse.eval nodeValue4224 (mixedVector B) := by
    change mixedMoment B node4224 node4224Labels = _
    exact sound4224 B hB hF
  have h4256 : mixedVector B (Sum.inr 4256) = Sparse.eval nodeValue4256 (mixedVector B) := by
    change mixedMoment B node4256 node4256Labels = _
    exact sound4256 B hB hF
  have h4635 : mixedVector B (Sum.inr 4635) = Sparse.eval nodeValue4635 (mixedVector B) := by
    change mixedMoment B node4635 node4635Labels = _
    exact sound4635 B hB hF
  have h4637 : mixedVector B (Sum.inr 4637) = Sparse.eval nodeValue4637 (mixedVector B) := by
    change mixedMoment B node4637 node4637Labels = _
    exact sound4637 B hB hF
  have h4654 : mixedVector B (Sum.inr 4654) = Sparse.eval nodeValue4654 (mixedVector B) := by
    change mixedMoment B node4654 node4654Labels = _
    exact sound4654 B hB hF
  have h4706 : mixedVector B (Sum.inr 4706) = Sparse.eval nodeValue4706 (mixedVector B) := by
    change mixedMoment B node4706 node4706Labels = _
    exact sound4706 B hB hF
  have h4717 : mixedVector B (Sum.inr 4717) = Sparse.eval nodeValue4717 (mixedVector B) := by
    change mixedMoment B node4717 node4717Labels = _
    exact sound4717 B hB hF
  have h4732 : mixedVector B (Sum.inr 4732) = Sparse.eval nodeValue4732 (mixedVector B) := by
    change mixedMoment B node4732 node4732Labels = _
    exact sound4732 B hB hF
  have h4767 : mixedVector B (Sum.inr 4767) = Sparse.eval nodeValue4767 (mixedVector B) := by
    change mixedMoment B node4767 node4767Labels = _
    exact sound4767 B hB hF
  have h4769 : mixedVector B (Sum.inr 4769) = Sparse.eval nodeValue4769 (mixedVector B) := by
    change mixedMoment B node4769 node4769Labels = _
    exact sound4769 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h5356 : mixedVector B (Sum.inr 5356) = Sparse.eval nodeValue5356 (mixedVector B) := by
    change mixedMoment B node5356 node5356Labels = _
    exact sound5356 B hB hF
  have h5393 : mixedVector B (Sum.inr 5393) = Sparse.eval nodeValue5393 (mixedVector B) := by
    change mixedMoment B node5393 node5393Labels = _
    exact sound5393 B hB hF
  have h5418 : mixedVector B (Sum.inr 5418) = Sparse.eval nodeValue5418 (mixedVector B) := by
    change mixedMoment B node5418 node5418Labels = _
    exact sound5418 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  simpa only [sourceForm2289, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4201, h4204, h4224, h4256, h4635, h4637, h4654, h4706, h4717, h4732, h4767, h4769, h4802, h4804, h4811, h4835, h4888, h5356, h5393, h5418, h5434, reducedSource1871] using sourceEq2289 B hB

theorem rowSound1871 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1871 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1871, numericCheck1871, reducedZero1871 B hB hF, mul_zero]

theorem sourceRowsAt1856 : MixedData.sourceRows (1856 : Fin 2425) =
    MixedData.row1856 := by decide +kernel

theorem sourceRowsAt1857 : MixedData.sourceRows (1857 : Fin 2425) =
    MixedData.row1857 := by decide +kernel

theorem sourceRowsAt1858 : MixedData.sourceRows (1858 : Fin 2425) =
    MixedData.row1858 := by decide +kernel

theorem sourceRowsAt1859 : MixedData.sourceRows (1859 : Fin 2425) =
    MixedData.row1859 := by decide +kernel

theorem sourceRowsAt1860 : MixedData.sourceRows (1860 : Fin 2425) =
    MixedData.row1860 := by decide +kernel

theorem sourceRowsAt1861 : MixedData.sourceRows (1861 : Fin 2425) =
    MixedData.row1861 := by decide +kernel

theorem sourceRowsAt1862 : MixedData.sourceRows (1862 : Fin 2425) =
    MixedData.row1862 := by decide +kernel

theorem sourceRowsAt1863 : MixedData.sourceRows (1863 : Fin 2425) =
    MixedData.row1863 := by decide +kernel

theorem sourceRowsAt1864 : MixedData.sourceRows (1864 : Fin 2425) =
    MixedData.row1864 := by decide +kernel

theorem sourceRowsAt1865 : MixedData.sourceRows (1865 : Fin 2425) =
    MixedData.row1865 := by decide +kernel

theorem sourceRowsAt1866 : MixedData.sourceRows (1866 : Fin 2425) =
    MixedData.row1866 := by decide +kernel

theorem sourceRowsAt1867 : MixedData.sourceRows (1867 : Fin 2425) =
    MixedData.row1867 := by decide +kernel

theorem sourceRowsAt1868 : MixedData.sourceRows (1868 : Fin 2425) =
    MixedData.row1868 := by decide +kernel

theorem sourceRowsAt1869 : MixedData.sourceRows (1869 : Fin 2425) =
    MixedData.row1869 := by decide +kernel

theorem sourceRowsAt1870 : MixedData.sourceRows (1870 : Fin 2425) =
    MixedData.row1870 := by decide +kernel

theorem sourceRowsAt1871 : MixedData.sourceRows (1871 : Fin 2425) =
    MixedData.row1871 := by decide +kernel

theorem chunkSound116 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 116) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1856 ∨ k.val = 1857 ∨ k.val = 1858 ∨ k.val = 1859 ∨ k.val = 1860 ∨ k.val = 1861 ∨ k.val = 1862 ∨ k.val = 1863 ∨ k.val = 1864 ∨ k.val = 1865 ∨ k.val = 1866 ∨ k.val = 1867 ∨ k.val = 1868 ∨ k.val = 1869 ∨ k.val = 1870 ∨ k.val = 1871 := by omega
  rcases heq with h1856 | h1857 | h1858 | h1859 | h1860 | h1861 | h1862 | h1863 | h1864 | h1865 | h1866 | h1867 | h1868 | h1869 | h1870 | h1871
  · have he : k = (1856 : Fin 2425) := Fin.ext h1856
    subst k
    rw [sourceRowsAt1856]
    exact rowSound1856 B hB hF
  · have he : k = (1857 : Fin 2425) := Fin.ext h1857
    subst k
    rw [sourceRowsAt1857]
    exact rowSound1857 B hB hF
  · have he : k = (1858 : Fin 2425) := Fin.ext h1858
    subst k
    rw [sourceRowsAt1858]
    exact rowSound1858 B hB hF
  · have he : k = (1859 : Fin 2425) := Fin.ext h1859
    subst k
    rw [sourceRowsAt1859]
    exact rowSound1859 B hB hF
  · have he : k = (1860 : Fin 2425) := Fin.ext h1860
    subst k
    rw [sourceRowsAt1860]
    exact rowSound1860 B hB hF
  · have he : k = (1861 : Fin 2425) := Fin.ext h1861
    subst k
    rw [sourceRowsAt1861]
    exact rowSound1861 B hB hF
  · have he : k = (1862 : Fin 2425) := Fin.ext h1862
    subst k
    rw [sourceRowsAt1862]
    exact rowSound1862 B hB hF
  · have he : k = (1863 : Fin 2425) := Fin.ext h1863
    subst k
    rw [sourceRowsAt1863]
    exact rowSound1863 B hB hF
  · have he : k = (1864 : Fin 2425) := Fin.ext h1864
    subst k
    rw [sourceRowsAt1864]
    exact rowSound1864 B hB hF
  · have he : k = (1865 : Fin 2425) := Fin.ext h1865
    subst k
    rw [sourceRowsAt1865]
    exact rowSound1865 B hB hF
  · have he : k = (1866 : Fin 2425) := Fin.ext h1866
    subst k
    rw [sourceRowsAt1866]
    exact rowSound1866 B hB hF
  · have he : k = (1867 : Fin 2425) := Fin.ext h1867
    subst k
    rw [sourceRowsAt1867]
    exact rowSound1867 B hB hF
  · have he : k = (1868 : Fin 2425) := Fin.ext h1868
    subst k
    rw [sourceRowsAt1868]
    exact rowSound1868 B hB hF
  · have he : k = (1869 : Fin 2425) := Fin.ext h1869
    subst k
    rw [sourceRowsAt1869]
    exact rowSound1869 B hB hF
  · have he : k = (1870 : Fin 2425) := Fin.ext h1870
    subst k
    rw [sourceRowsAt1870]
    exact rowSound1870 B hB hF
  · have he : k = (1871 : Fin 2425) := Fin.ext h1871
    subst k
    rw [sourceRowsAt1871]
    exact rowSound1871 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
