import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic115
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources70

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1840 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1840 (mixedVector B) = 0 := by
  have h1321 : mixedVector B (Sum.inr 1321) = Sparse.eval nodeValue1321 (mixedVector B) := by
    change mixedMoment B node1321 node1321Labels = _
    exact sound1321 B hB hF
  have h1323 : mixedVector B (Sum.inr 1323) = Sparse.eval nodeValue1323 (mixedVector B) := by
    change mixedMoment B node1323 node1323Labels = _
    exact sound1323 B hB hF
  have h1325 : mixedVector B (Sum.inr 1325) = Sparse.eval nodeValue1325 (mixedVector B) := by
    change mixedMoment B node1325 node1325Labels = _
    exact sound1325 B hB hF
  have h1419 : mixedVector B (Sum.inr 1419) = Sparse.eval nodeValue1419 (mixedVector B) := by
    change mixedMoment B node1419 node1419Labels = _
    exact sound1419 B hB hF
  have h1813 : mixedVector B (Sum.inr 1813) = Sparse.eval nodeValue1813 (mixedVector B) := by
    change mixedMoment B node1813 node1813Labels = _
    exact sound1813 B hB hF
  have h1820 : mixedVector B (Sum.inr 1820) = Sparse.eval nodeValue1820 (mixedVector B) := by
    change mixedMoment B node1820 node1820Labels = _
    exact sound1820 B hB hF
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2816 : mixedVector B (Sum.inr 2816) = Sparse.eval nodeValue2816 (mixedVector B) := by
    change mixedMoment B node2816 node2816Labels = _
    exact sound2816 B hB hF
  have h2821 : mixedVector B (Sum.inr 2821) = Sparse.eval nodeValue2821 (mixedVector B) := by
    change mixedMoment B node2821 node2821Labels = _
    exact sound2821 B hB hF
  have h2966 : mixedVector B (Sum.inr 2966) = Sparse.eval nodeValue2966 (mixedVector B) := by
    change mixedMoment B node2966 node2966Labels = _
    exact sound2966 B hB hF
  have h3040 : mixedVector B (Sum.inr 3040) = Sparse.eval nodeValue3040 (mixedVector B) := by
    change mixedMoment B node3040 node3040Labels = _
    exact sound3040 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3056 : mixedVector B (Sum.inr 3056) = Sparse.eval nodeValue3056 (mixedVector B) := by
    change mixedMoment B node3056 node3056Labels = _
    exact sound3056 B hB hF
  have h3103 : mixedVector B (Sum.inr 3103) = Sparse.eval nodeValue3103 (mixedVector B) := by
    change mixedMoment B node3103 node3103Labels = _
    exact sound3103 B hB hF
  have h3131 : mixedVector B (Sum.inr 3131) = Sparse.eval nodeValue3131 (mixedVector B) := by
    change mixedMoment B node3131 node3131Labels = _
    exact sound3131 B hB hF
  have h3163 : mixedVector B (Sum.inr 3163) = Sparse.eval nodeValue3163 (mixedVector B) := by
    change mixedMoment B node3163 node3163Labels = _
    exact sound3163 B hB hF
  have h3180 : mixedVector B (Sum.inr 3180) = Sparse.eval nodeValue3180 (mixedVector B) := by
    change mixedMoment B node3180 node3180Labels = _
    exact sound3180 B hB hF
  have h3185 : mixedVector B (Sum.inr 3185) = Sparse.eval nodeValue3185 (mixedVector B) := by
    change mixedMoment B node3185 node3185Labels = _
    exact sound3185 B hB hF
  have h3206 : mixedVector B (Sum.inr 3206) = Sparse.eval nodeValue3206 (mixedVector B) := by
    change mixedMoment B node3206 node3206Labels = _
    exact sound3206 B hB hF
  have h3225 : mixedVector B (Sum.inr 3225) = Sparse.eval nodeValue3225 (mixedVector B) := by
    change mixedMoment B node3225 node3225Labels = _
    exact sound3225 B hB hF
  have h3230 : mixedVector B (Sum.inr 3230) = Sparse.eval nodeValue3230 (mixedVector B) := by
    change mixedMoment B node3230 node3230Labels = _
    exact sound3230 B hB hF
  simpa only [sourceForm2252, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1321, h1323, h1325, h1419, h1813, h1820, h2113, h2816, h2821, h2966, h3040, h3055, h3056, h3103, h3131, h3163, h3180, h3185, h3206, h3225, h3230, reducedSource1840] using sourceEq2252 B hB

theorem rowSound1840 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1840 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1840, numericCheck1840, reducedZero1840 B hB hF, mul_zero]

theorem reducedZero1841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1841 (mixedVector B) = 0 := by
  have h1712 : mixedVector B (Sum.inr 1712) = Sparse.eval nodeValue1712 (mixedVector B) := by
    change mixedMoment B node1712 node1712Labels = _
    exact sound1712 B hB hF
  have h1735 : mixedVector B (Sum.inr 1735) = Sparse.eval nodeValue1735 (mixedVector B) := by
    change mixedMoment B node1735 node1735Labels = _
    exact sound1735 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h1743 : mixedVector B (Sum.inr 1743) = Sparse.eval nodeValue1743 (mixedVector B) := by
    change mixedMoment B node1743 node1743Labels = _
    exact sound1743 B hB hF
  have h2162 : mixedVector B (Sum.inr 2162) = Sparse.eval nodeValue2162 (mixedVector B) := by
    change mixedMoment B node2162 node2162Labels = _
    exact sound2162 B hB hF
  have h2163 : mixedVector B (Sum.inr 2163) = Sparse.eval nodeValue2163 (mixedVector B) := by
    change mixedMoment B node2163 node2163Labels = _
    exact sound2163 B hB hF
  have h2194 : mixedVector B (Sum.inr 2194) = Sparse.eval nodeValue2194 (mixedVector B) := by
    change mixedMoment B node2194 node2194Labels = _
    exact sound2194 B hB hF
  have h2212 : mixedVector B (Sum.inr 2212) = Sparse.eval nodeValue2212 (mixedVector B) := by
    change mixedMoment B node2212 node2212Labels = _
    exact sound2212 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h2249 : mixedVector B (Sum.inr 2249) = Sparse.eval nodeValue2249 (mixedVector B) := by
    change mixedMoment B node2249 node2249Labels = _
    exact sound2249 B hB hF
  have h2251 : mixedVector B (Sum.inr 2251) = Sparse.eval nodeValue2251 (mixedVector B) := by
    change mixedMoment B node2251 node2251Labels = _
    exact sound2251 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2273 : mixedVector B (Sum.inr 2273) = Sparse.eval nodeValue2273 (mixedVector B) := by
    change mixedMoment B node2273 node2273Labels = _
    exact sound2273 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2282 : mixedVector B (Sum.inr 2282) = Sparse.eval nodeValue2282 (mixedVector B) := by
    change mixedMoment B node2282 node2282Labels = _
    exact sound2282 B hB hF
  have h2729 : mixedVector B (Sum.inr 2729) = Sparse.eval nodeValue2729 (mixedVector B) := by
    change mixedMoment B node2729 node2729Labels = _
    exact sound2729 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2771 : mixedVector B (Sum.inr 2771) = Sparse.eval nodeValue2771 (mixedVector B) := by
    change mixedMoment B node2771 node2771Labels = _
    exact sound2771 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  simpa only [sourceForm2253, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1712, h1735, h1738, h1743, h2162, h2163, h2194, h2212, h2215, h2242, h2249, h2251, h2261, h2264, h2273, h2278, h2282, h2729, h2765, h2771, h2774, reducedSource1841] using sourceEq2253 B hB

theorem rowSound1841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1841 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1841, numericCheck1841, reducedZero1841 B hB hF, mul_zero]

theorem reducedZero1842 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1842 (mixedVector B) = 0 := by
  have h1826 : mixedVector B (Sum.inr 1826) = Sparse.eval nodeValue1826 (mixedVector B) := by
    change mixedMoment B node1826 node1826Labels = _
    exact sound1826 B hB hF
  have h1830 : mixedVector B (Sum.inr 1830) = Sparse.eval nodeValue1830 (mixedVector B) := by
    change mixedMoment B node1830 node1830Labels = _
    exact sound1830 B hB hF
  have h1832 : mixedVector B (Sum.inr 1832) = Sparse.eval nodeValue1832 (mixedVector B) := by
    change mixedMoment B node1832 node1832Labels = _
    exact sound1832 B hB hF
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h3056 : mixedVector B (Sum.inr 3056) = Sparse.eval nodeValue3056 (mixedVector B) := by
    change mixedMoment B node3056 node3056Labels = _
    exact sound3056 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2254, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1826, h1830, h1832, h2115, h3056, h4084, reducedSource1842] using sourceEq2254 B hB

theorem rowSound1842 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1842 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1842, numericCheck1842, reducedZero1842 B hB hF, mul_zero]

theorem reducedZero1843 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1843 (mixedVector B) = 0 := by
  have h946 : mixedVector B (Sum.inr 946) = Sparse.eval nodeValue946 (mixedVector B) := by
    change mixedMoment B node946 node946Labels = _
    exact sound946 B hB hF
  have h1826 : mixedVector B (Sum.inr 1826) = Sparse.eval nodeValue1826 (mixedVector B) := by
    change mixedMoment B node1826 node1826Labels = _
    exact sound1826 B hB hF
  have h1974 : mixedVector B (Sum.inr 1974) = Sparse.eval nodeValue1974 (mixedVector B) := by
    change mixedMoment B node1974 node1974Labels = _
    exact sound1974 B hB hF
  have h2106 : mixedVector B (Sum.inr 2106) = Sparse.eval nodeValue2106 (mixedVector B) := by
    change mixedMoment B node2106 node2106Labels = _
    exact sound2106 B hB hF
  have h2108 : mixedVector B (Sum.inr 2108) = Sparse.eval nodeValue2108 (mixedVector B) := by
    change mixedMoment B node2108 node2108Labels = _
    exact sound2108 B hB hF
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2255, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h946, h1826, h1974, h2106, h2108, h2115, h4084, reducedSource1843] using sourceEq2255 B hB

theorem rowSound1843 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1843 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1843, numericCheck1843, reducedZero1843 B hB hF, mul_zero]

theorem reducedZero1844 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1844 (mixedVector B) = 0 := by
  have h4238 : mixedVector B (Sum.inr 4238) = Sparse.eval nodeValue4238 (mixedVector B) := by
    change mixedMoment B node4238 node4238Labels = _
    exact sound4238 B hB hF
  have h4241 : mixedVector B (Sum.inr 4241) = Sparse.eval nodeValue4241 (mixedVector B) := by
    change mixedMoment B node4241 node4241Labels = _
    exact sound4241 B hB hF
  have h4243 : mixedVector B (Sum.inr 4243) = Sparse.eval nodeValue4243 (mixedVector B) := by
    change mixedMoment B node4243 node4243Labels = _
    exact sound4243 B hB hF
  have h4278 : mixedVector B (Sum.inr 4278) = Sparse.eval nodeValue4278 (mixedVector B) := by
    change mixedMoment B node4278 node4278Labels = _
    exact sound4278 B hB hF
  have h4673 : mixedVector B (Sum.inr 4673) = Sparse.eval nodeValue4673 (mixedVector B) := by
    change mixedMoment B node4673 node4673Labels = _
    exact sound4673 B hB hF
  have h4688 : mixedVector B (Sum.inr 4688) = Sparse.eval nodeValue4688 (mixedVector B) := by
    change mixedMoment B node4688 node4688Labels = _
    exact sound4688 B hB hF
  have h4691 : mixedVector B (Sum.inr 4691) = Sparse.eval nodeValue4691 (mixedVector B) := by
    change mixedMoment B node4691 node4691Labels = _
    exact sound4691 B hB hF
  have h4693 : mixedVector B (Sum.inr 4693) = Sparse.eval nodeValue4693 (mixedVector B) := by
    change mixedMoment B node4693 node4693Labels = _
    exact sound4693 B hB hF
  have h4724 : mixedVector B (Sum.inr 4724) = Sparse.eval nodeValue4724 (mixedVector B) := by
    change mixedMoment B node4724 node4724Labels = _
    exact sound4724 B hB hF
  have h4727 : mixedVector B (Sum.inr 4727) = Sparse.eval nodeValue4727 (mixedVector B) := by
    change mixedMoment B node4727 node4727Labels = _
    exact sound4727 B hB hF
  have h4749 : mixedVector B (Sum.inr 4749) = Sparse.eval nodeValue4749 (mixedVector B) := by
    change mixedMoment B node4749 node4749Labels = _
    exact sound4749 B hB hF
  have h4860 : mixedVector B (Sum.inr 4860) = Sparse.eval nodeValue4860 (mixedVector B) := by
    change mixedMoment B node4860 node4860Labels = _
    exact sound4860 B hB hF
  have h4862 : mixedVector B (Sum.inr 4862) = Sparse.eval nodeValue4862 (mixedVector B) := by
    change mixedMoment B node4862 node4862Labels = _
    exact sound4862 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4874 : mixedVector B (Sum.inr 4874) = Sparse.eval nodeValue4874 (mixedVector B) := by
    change mixedMoment B node4874 node4874Labels = _
    exact sound4874 B hB hF
  have h4898 : mixedVector B (Sum.inr 4898) = Sparse.eval nodeValue4898 (mixedVector B) := by
    change mixedMoment B node4898 node4898Labels = _
    exact sound4898 B hB hF
  have h5384 : mixedVector B (Sum.inr 5384) = Sparse.eval nodeValue5384 (mixedVector B) := by
    change mixedMoment B node5384 node5384Labels = _
    exact sound5384 B hB hF
  have h5389 : mixedVector B (Sum.inr 5389) = Sparse.eval nodeValue5389 (mixedVector B) := by
    change mixedMoment B node5389 node5389Labels = _
    exact sound5389 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  have h5449 : mixedVector B (Sum.inr 5449) = Sparse.eval nodeValue5449 (mixedVector B) := by
    change mixedMoment B node5449 node5449Labels = _
    exact sound5449 B hB hF
  simpa only [sourceForm2256, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4238, h4241, h4243, h4278, h4673, h4688, h4691, h4693, h4724, h4727, h4749, h4860, h4862, h4869, h4871, h4874, h4898, h5384, h5389, h5443, h5449, reducedSource1844] using sourceEq2256 B hB

theorem rowSound1844 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1844 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1844, numericCheck1844, reducedZero1844 B hB hF, mul_zero]

theorem reducedZero1845 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1845 (mixedVector B) = 0 := by
  have h738 : mixedVector B (Sum.inr 738) = Sparse.eval nodeValue738 (mixedVector B) := by
    change mixedMoment B node738 node738Labels = _
    exact sound738 B hB hF
  have h741 : mixedVector B (Sum.inr 741) = Sparse.eval nodeValue741 (mixedVector B) := by
    change mixedMoment B node741 node741Labels = _
    exact sound741 B hB hF
  have h743 : mixedVector B (Sum.inr 743) = Sparse.eval nodeValue743 (mixedVector B) := by
    change mixedMoment B node743 node743Labels = _
    exact sound743 B hB hF
  have h830 : mixedVector B (Sum.inr 830) = Sparse.eval nodeValue830 (mixedVector B) := by
    change mixedMoment B node830 node830Labels = _
    exact sound830 B hB hF
  have h1799 : mixedVector B (Sum.inr 1799) = Sparse.eval nodeValue1799 (mixedVector B) := by
    change mixedMoment B node1799 node1799Labels = _
    exact sound1799 B hB hF
  have h1814 : mixedVector B (Sum.inr 1814) = Sparse.eval nodeValue1814 (mixedVector B) := by
    change mixedMoment B node1814 node1814Labels = _
    exact sound1814 B hB hF
  have h1817 : mixedVector B (Sum.inr 1817) = Sparse.eval nodeValue1817 (mixedVector B) := by
    change mixedMoment B node1817 node1817Labels = _
    exact sound1817 B hB hF
  have h1819 : mixedVector B (Sum.inr 1819) = Sparse.eval nodeValue1819 (mixedVector B) := by
    change mixedMoment B node1819 node1819Labels = _
    exact sound1819 B hB hF
  have h1878 : mixedVector B (Sum.inr 1878) = Sparse.eval nodeValue1878 (mixedVector B) := by
    change mixedMoment B node1878 node1878Labels = _
    exact sound1878 B hB hF
  have h1881 : mixedVector B (Sum.inr 1881) = Sparse.eval nodeValue1881 (mixedVector B) := by
    change mixedMoment B node1881 node1881Labels = _
    exact sound1881 B hB hF
  have h1928 : mixedVector B (Sum.inr 1928) = Sparse.eval nodeValue1928 (mixedVector B) := by
    change mixedMoment B node1928 node1928Labels = _
    exact sound1928 B hB hF
  have h2101 : mixedVector B (Sum.inr 2101) = Sparse.eval nodeValue2101 (mixedVector B) := by
    change mixedMoment B node2101 node2101Labels = _
    exact sound2101 B hB hF
  have h2103 : mixedVector B (Sum.inr 2103) = Sparse.eval nodeValue2103 (mixedVector B) := by
    change mixedMoment B node2103 node2103Labels = _
    exact sound2103 B hB hF
  have h2110 : mixedVector B (Sum.inr 2110) = Sparse.eval nodeValue2110 (mixedVector B) := by
    change mixedMoment B node2110 node2110Labels = _
    exact sound2110 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h3740 : mixedVector B (Sum.inr 3740) = Sparse.eval nodeValue3740 (mixedVector B) := by
    change mixedMoment B node3740 node3740Labels = _
    exact sound3740 B hB hF
  have h3886 : mixedVector B (Sum.inr 3886) = Sparse.eval nodeValue3886 (mixedVector B) := by
    change mixedMoment B node3886 node3886Labels = _
    exact sound3886 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  simpa only [sourceForm2257, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h738, h741, h743, h830, h1799, h1814, h1817, h1819, h1878, h1881, h1928, h2101, h2103, h2110, h2112, h2276, h2279, h3732, h3740, h3886, h3889, reducedSource1845] using sourceEq2257 B hB

theorem rowSound1845 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1845 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1845, numericCheck1845, reducedZero1845 B hB hF, mul_zero]

theorem reducedZero1846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1846 (mixedVector B) = 0 := by
  have h1640 : mixedVector B (Sum.inr 1640) = Sparse.eval nodeValue1640 (mixedVector B) := by
    change mixedMoment B node1640 node1640Labels = _
    exact sound1640 B hB hF
  have h1652 : mixedVector B (Sum.inr 1652) = Sparse.eval nodeValue1652 (mixedVector B) := by
    change mixedMoment B node1652 node1652Labels = _
    exact sound1652 B hB hF
  have h1653 : mixedVector B (Sum.inr 1653) = Sparse.eval nodeValue1653 (mixedVector B) := by
    change mixedMoment B node1653 node1653Labels = _
    exact sound1653 B hB hF
  have h1660 : mixedVector B (Sum.inr 1660) = Sparse.eval nodeValue1660 (mixedVector B) := by
    change mixedMoment B node1660 node1660Labels = _
    exact sound1660 B hB hF
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h2065 : mixedVector B (Sum.inr 2065) = Sparse.eval nodeValue2065 (mixedVector B) := by
    change mixedMoment B node2065 node2065Labels = _
    exact sound2065 B hB hF
  have h2066 : mixedVector B (Sum.inr 2066) = Sparse.eval nodeValue2066 (mixedVector B) := by
    change mixedMoment B node2066 node2066Labels = _
    exact sound2066 B hB hF
  have h2072 : mixedVector B (Sum.inr 2072) = Sparse.eval nodeValue2072 (mixedVector B) := by
    change mixedMoment B node2072 node2072Labels = _
    exact sound2072 B hB hF
  have h2081 : mixedVector B (Sum.inr 2081) = Sparse.eval nodeValue2081 (mixedVector B) := by
    change mixedMoment B node2081 node2081Labels = _
    exact sound2081 B hB hF
  have h2082 : mixedVector B (Sum.inr 2082) = Sparse.eval nodeValue2082 (mixedVector B) := by
    change mixedMoment B node2082 node2082Labels = _
    exact sound2082 B hB hF
  have h2093 : mixedVector B (Sum.inr 2093) = Sparse.eval nodeValue2093 (mixedVector B) := by
    change mixedMoment B node2093 node2093Labels = _
    exact sound2093 B hB hF
  have h2094 : mixedVector B (Sum.inr 2094) = Sparse.eval nodeValue2094 (mixedVector B) := by
    change mixedMoment B node2094 node2094Labels = _
    exact sound2094 B hB hF
  have h2114 : mixedVector B (Sum.inr 2114) = Sparse.eval nodeValue2114 (mixedVector B) := by
    change mixedMoment B node2114 node2114Labels = _
    exact sound2114 B hB hF
  have h2116 : mixedVector B (Sum.inr 2116) = Sparse.eval nodeValue2116 (mixedVector B) := by
    change mixedMoment B node2116 node2116Labels = _
    exact sound2116 B hB hF
  have h2122 : mixedVector B (Sum.inr 2122) = Sparse.eval nodeValue2122 (mixedVector B) := by
    change mixedMoment B node2122 node2122Labels = _
    exact sound2122 B hB hF
  have h2137 : mixedVector B (Sum.inr 2137) = Sparse.eval nodeValue2137 (mixedVector B) := by
    change mixedMoment B node2137 node2137Labels = _
    exact sound2137 B hB hF
  have h2138 : mixedVector B (Sum.inr 2138) = Sparse.eval nodeValue2138 (mixedVector B) := by
    change mixedMoment B node2138 node2138Labels = _
    exact sound2138 B hB hF
  have h2604 : mixedVector B (Sum.inr 2604) = Sparse.eval nodeValue2604 (mixedVector B) := by
    change mixedMoment B node2604 node2604Labels = _
    exact sound2604 B hB hF
  have h2620 : mixedVector B (Sum.inr 2620) = Sparse.eval nodeValue2620 (mixedVector B) := by
    change mixedMoment B node2620 node2620Labels = _
    exact sound2620 B hB hF
  have h2643 : mixedVector B (Sum.inr 2643) = Sparse.eval nodeValue2643 (mixedVector B) := by
    change mixedMoment B node2643 node2643Labels = _
    exact sound2643 B hB hF
  have h2644 : mixedVector B (Sum.inr 2644) = Sparse.eval nodeValue2644 (mixedVector B) := by
    change mixedMoment B node2644 node2644Labels = _
    exact sound2644 B hB hF
  simpa only [sourceForm2259, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1640, h1652, h1653, h1660, h2028, h2065, h2066, h2072, h2081, h2082, h2093, h2094, h2114, h2116, h2122, h2137, h2138, h2604, h2620, h2643, h2644, reducedSource1846] using sourceEq2259 B hB

theorem rowSound1846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1846 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1846, numericCheck1846, reducedZero1846 B hB hF, mul_zero]

theorem reducedZero1847 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1847 (mixedVector B) = 0 := by
  have h1371 : mixedVector B (Sum.inr 1371) = Sparse.eval nodeValue1371 (mixedVector B) := by
    change mixedMoment B node1371 node1371Labels = _
    exact sound1371 B hB hF
  have h1373 : mixedVector B (Sum.inr 1373) = Sparse.eval nodeValue1373 (mixedVector B) := by
    change mixedMoment B node1373 node1373Labels = _
    exact sound1373 B hB hF
  have h1374 : mixedVector B (Sum.inr 1374) = Sparse.eval nodeValue1374 (mixedVector B) := by
    change mixedMoment B node1374 node1374Labels = _
    exact sound1374 B hB hF
  have h1444 : mixedVector B (Sum.inr 1444) = Sparse.eval nodeValue1444 (mixedVector B) := by
    change mixedMoment B node1444 node1444Labels = _
    exact sound1444 B hB hF
  have h2867 : mixedVector B (Sum.inr 2867) = Sparse.eval nodeValue2867 (mixedVector B) := by
    change mixedMoment B node2867 node2867Labels = _
    exact sound2867 B hB hF
  have h2872 : mixedVector B (Sum.inr 2872) = Sparse.eval nodeValue2872 (mixedVector B) := by
    change mixedMoment B node2872 node2872Labels = _
    exact sound2872 B hB hF
  have h2887 : mixedVector B (Sum.inr 2887) = Sparse.eval nodeValue2887 (mixedVector B) := by
    change mixedMoment B node2887 node2887Labels = _
    exact sound2887 B hB hF
  have h2888 : mixedVector B (Sum.inr 2888) = Sparse.eval nodeValue2888 (mixedVector B) := by
    change mixedMoment B node2888 node2888Labels = _
    exact sound2888 B hB hF
  have h2889 : mixedVector B (Sum.inr 2889) = Sparse.eval nodeValue2889 (mixedVector B) := by
    change mixedMoment B node2889 node2889Labels = _
    exact sound2889 B hB hF
  have h2968 : mixedVector B (Sum.inr 2968) = Sparse.eval nodeValue2968 (mixedVector B) := by
    change mixedMoment B node2968 node2968Labels = _
    exact sound2968 B hB hF
  have h3095 : mixedVector B (Sum.inr 3095) = Sparse.eval nodeValue3095 (mixedVector B) := by
    change mixedMoment B node3095 node3095Labels = _
    exact sound3095 B hB hF
  have h3151 : mixedVector B (Sum.inr 3151) = Sparse.eval nodeValue3151 (mixedVector B) := by
    change mixedMoment B node3151 node3151Labels = _
    exact sound3151 B hB hF
  have h3159 : mixedVector B (Sum.inr 3159) = Sparse.eval nodeValue3159 (mixedVector B) := by
    change mixedMoment B node3159 node3159Labels = _
    exact sound3159 B hB hF
  have h3160 : mixedVector B (Sum.inr 3160) = Sparse.eval nodeValue3160 (mixedVector B) := by
    change mixedMoment B node3160 node3160Labels = _
    exact sound3160 B hB hF
  have h3161 : mixedVector B (Sum.inr 3161) = Sparse.eval nodeValue3161 (mixedVector B) := by
    change mixedMoment B node3161 node3161Labels = _
    exact sound3161 B hB hF
  have h3168 : mixedVector B (Sum.inr 3168) = Sparse.eval nodeValue3168 (mixedVector B) := by
    change mixedMoment B node3168 node3168Labels = _
    exact sound3168 B hB hF
  have h3174 : mixedVector B (Sum.inr 3174) = Sparse.eval nodeValue3174 (mixedVector B) := by
    change mixedMoment B node3174 node3174Labels = _
    exact sound3174 B hB hF
  have h3178 : mixedVector B (Sum.inr 3178) = Sparse.eval nodeValue3178 (mixedVector B) := by
    change mixedMoment B node3178 node3178Labels = _
    exact sound3178 B hB hF
  have h3188 : mixedVector B (Sum.inr 3188) = Sparse.eval nodeValue3188 (mixedVector B) := by
    change mixedMoment B node3188 node3188Labels = _
    exact sound3188 B hB hF
  have h3206 : mixedVector B (Sum.inr 3206) = Sparse.eval nodeValue3206 (mixedVector B) := by
    change mixedMoment B node3206 node3206Labels = _
    exact sound3206 B hB hF
  have h3216 : mixedVector B (Sum.inr 3216) = Sparse.eval nodeValue3216 (mixedVector B) := by
    change mixedMoment B node3216 node3216Labels = _
    exact sound3216 B hB hF
  simpa only [sourceForm2260, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1371, h1373, h1374, h1444, h2867, h2872, h2887, h2888, h2889, h2968, h3095, h3151, h3159, h3160, h3161, h3168, h3174, h3178, h3188, h3206, h3216, reducedSource1847] using sourceEq2260 B hB

theorem rowSound1847 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1847 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1847, numericCheck1847, reducedZero1847 B hB hF, mul_zero]

theorem reducedZero1848 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1848 (mixedVector B) = 0 := by
  have h4369 : mixedVector B (Sum.inr 4369) = Sparse.eval nodeValue4369 (mixedVector B) := by
    change mixedMoment B node4369 node4369Labels = _
    exact sound4369 B hB hF
  have h4374 : mixedVector B (Sum.inr 4374) = Sparse.eval nodeValue4374 (mixedVector B) := by
    change mixedMoment B node4374 node4374Labels = _
    exact sound4374 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4701 : mixedVector B (Sum.inr 4701) = Sparse.eval nodeValue4701 (mixedVector B) := by
    change mixedMoment B node4701 node4701Labels = _
    exact sound4701 B hB hF
  have h4705 : mixedVector B (Sum.inr 4705) = Sparse.eval nodeValue4705 (mixedVector B) := by
    change mixedMoment B node4705 node4705Labels = _
    exact sound4705 B hB hF
  have h4774 : mixedVector B (Sum.inr 4774) = Sparse.eval nodeValue4774 (mixedVector B) := by
    change mixedMoment B node4774 node4774Labels = _
    exact sound4774 B hB hF
  have h4777 : mixedVector B (Sum.inr 4777) = Sparse.eval nodeValue4777 (mixedVector B) := by
    change mixedMoment B node4777 node4777Labels = _
    exact sound4777 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h5269 : mixedVector B (Sum.inr 5269) = Sparse.eval nodeValue5269 (mixedVector B) := by
    change mixedMoment B node5269 node5269Labels = _
    exact sound5269 B hB hF
  have h5303 : mixedVector B (Sum.inr 5303) = Sparse.eval nodeValue5303 (mixedVector B) := by
    change mixedMoment B node5303 node5303Labels = _
    exact sound5303 B hB hF
  have h5304 : mixedVector B (Sum.inr 5304) = Sparse.eval nodeValue5304 (mixedVector B) := by
    change mixedMoment B node5304 node5304Labels = _
    exact sound5304 B hB hF
  simpa only [sourceForm2261, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4369, h4374, h4467, h4701, h4705, h4774, h4777, h4811, h4866, h4871, h4895, h5269, h5303, h5304, reducedSource1848] using sourceEq2261 B hB

theorem rowSound1848 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1848 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1848, numericCheck1848, reducedZero1848 B hB hF, mul_zero]

theorem reducedZero1849 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1849 (mixedVector B) = 0 := by
  have h1322 : mixedVector B (Sum.inr 1322) = Sparse.eval nodeValue1322 (mixedVector B) := by
    change mixedMoment B node1322 node1322Labels = _
    exact sound1322 B hB hF
  have h1324 : mixedVector B (Sum.inr 1324) = Sparse.eval nodeValue1324 (mixedVector B) := by
    change mixedMoment B node1324 node1324Labels = _
    exact sound1324 B hB hF
  have h1420 : mixedVector B (Sum.inr 1420) = Sparse.eval nodeValue1420 (mixedVector B) := by
    change mixedMoment B node1420 node1420Labels = _
    exact sound1420 B hB hF
  have h2340 : mixedVector B (Sum.inr 2340) = Sparse.eval nodeValue2340 (mixedVector B) := by
    change mixedMoment B node2340 node2340Labels = _
    exact sound2340 B hB hF
  have h2346 : mixedVector B (Sum.inr 2346) = Sparse.eval nodeValue2346 (mixedVector B) := by
    change mixedMoment B node2346 node2346Labels = _
    exact sound2346 B hB hF
  have h2602 : mixedVector B (Sum.inr 2602) = Sparse.eval nodeValue2602 (mixedVector B) := by
    change mixedMoment B node2602 node2602Labels = _
    exact sound2602 B hB hF
  have h3108 : mixedVector B (Sum.inr 3108) = Sparse.eval nodeValue3108 (mixedVector B) := by
    change mixedMoment B node3108 node3108Labels = _
    exact sound3108 B hB hF
  have h3118 : mixedVector B (Sum.inr 3118) = Sparse.eval nodeValue3118 (mixedVector B) := by
    change mixedMoment B node3118 node3118Labels = _
    exact sound3118 B hB hF
  have h3119 : mixedVector B (Sum.inr 3119) = Sparse.eval nodeValue3119 (mixedVector B) := by
    change mixedMoment B node3119 node3119Labels = _
    exact sound3119 B hB hF
  have h3132 : mixedVector B (Sum.inr 3132) = Sparse.eval nodeValue3132 (mixedVector B) := by
    change mixedMoment B node3132 node3132Labels = _
    exact sound3132 B hB hF
  have h3164 : mixedVector B (Sum.inr 3164) = Sparse.eval nodeValue3164 (mixedVector B) := by
    change mixedMoment B node3164 node3164Labels = _
    exact sound3164 B hB hF
  have h3184 : mixedVector B (Sum.inr 3184) = Sparse.eval nodeValue3184 (mixedVector B) := by
    change mixedMoment B node3184 node3184Labels = _
    exact sound3184 B hB hF
  have h3207 : mixedVector B (Sum.inr 3207) = Sparse.eval nodeValue3207 (mixedVector B) := by
    change mixedMoment B node3207 node3207Labels = _
    exact sound3207 B hB hF
  have h3229 : mixedVector B (Sum.inr 3229) = Sparse.eval nodeValue3229 (mixedVector B) := by
    change mixedMoment B node3229 node3229Labels = _
    exact sound3229 B hB hF
  simpa only [sourceForm2262, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1322, h1324, h1420, h2340, h2346, h2602, h3108, h3118, h3119, h3132, h3164, h3184, h3207, h3229, reducedSource1849] using sourceEq2262 B hB

theorem rowSound1849 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1849 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1849, numericCheck1849, reducedZero1849 B hB hF, mul_zero]

theorem reducedZero1850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1850 (mixedVector B) = 0 := by
  have h1721 : mixedVector B (Sum.inr 1721) = Sparse.eval nodeValue1721 (mixedVector B) := by
    change mixedMoment B node1721 node1721Labels = _
    exact sound1721 B hB hF
  have h1748 : mixedVector B (Sum.inr 1748) = Sparse.eval nodeValue1748 (mixedVector B) := by
    change mixedMoment B node1748 node1748Labels = _
    exact sound1748 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h2199 : mixedVector B (Sum.inr 2199) = Sparse.eval nodeValue2199 (mixedVector B) := by
    change mixedMoment B node2199 node2199Labels = _
    exact sound2199 B hB hF
  have h2223 : mixedVector B (Sum.inr 2223) = Sparse.eval nodeValue2223 (mixedVector B) := by
    change mixedMoment B node2223 node2223Labels = _
    exact sound2223 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2257 : mixedVector B (Sum.inr 2257) = Sparse.eval nodeValue2257 (mixedVector B) := by
    change mixedMoment B node2257 node2257Labels = _
    exact sound2257 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2286 : mixedVector B (Sum.inr 2286) = Sparse.eval nodeValue2286 (mixedVector B) := by
    change mixedMoment B node2286 node2286Labels = _
    exact sound2286 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h2736 : mixedVector B (Sum.inr 2736) = Sparse.eval nodeValue2736 (mixedVector B) := by
    change mixedMoment B node2736 node2736Labels = _
    exact sound2736 B hB hF
  have h2779 : mixedVector B (Sum.inr 2779) = Sparse.eval nodeValue2779 (mixedVector B) := by
    change mixedMoment B node2779 node2779Labels = _
    exact sound2779 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  simpa only [sourceForm2263, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1721, h1748, h1751, h2199, h2223, h2225, h2257, h2260, h2286, h2287, h2291, h2736, h2779, h2782, reducedSource1850] using sourceEq2263 B hB

theorem rowSound1850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1850 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1850, numericCheck1850, reducedZero1850 B hB hF, mul_zero]

theorem reducedZero1851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1851 (mixedVector B) = 0 := by
  have h1827 : mixedVector B (Sum.inr 1827) = Sparse.eval nodeValue1827 (mixedVector B) := by
    change mixedMoment B node1827 node1827Labels = _
    exact sound1827 B hB hF
  have h1831 : mixedVector B (Sum.inr 1831) = Sparse.eval nodeValue1831 (mixedVector B) := by
    change mixedMoment B node1831 node1831Labels = _
    exact sound1831 B hB hF
  have h2116 : mixedVector B (Sum.inr 2116) = Sparse.eval nodeValue2116 (mixedVector B) := by
    change mixedMoment B node2116 node2116Labels = _
    exact sound2116 B hB hF
  have h3118 : mixedVector B (Sum.inr 3118) = Sparse.eval nodeValue3118 (mixedVector B) := by
    change mixedMoment B node3118 node3118Labels = _
    exact sound3118 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2264, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1827, h1831, h2116, h3118, h4083, reducedSource1851] using sourceEq2264 B hB

theorem rowSound1851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1851 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1851, numericCheck1851, reducedZero1851 B hB hF, mul_zero]

theorem reducedZero1852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1852 (mixedVector B) = 0 := by
  have h947 : mixedVector B (Sum.inr 947) = Sparse.eval nodeValue947 (mixedVector B) := by
    change mixedMoment B node947 node947Labels = _
    exact sound947 B hB hF
  have h1827 : mixedVector B (Sum.inr 1827) = Sparse.eval nodeValue1827 (mixedVector B) := by
    change mixedMoment B node1827 node1827Labels = _
    exact sound1827 B hB hF
  have h1975 : mixedVector B (Sum.inr 1975) = Sparse.eval nodeValue1975 (mixedVector B) := by
    change mixedMoment B node1975 node1975Labels = _
    exact sound1975 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h2116 : mixedVector B (Sum.inr 2116) = Sparse.eval nodeValue2116 (mixedVector B) := by
    change mixedMoment B node2116 node2116Labels = _
    exact sound2116 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2265, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h947, h1827, h1975, h2107, h2116, h4083, reducedSource1852] using sourceEq2265 B hB

theorem rowSound1852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1852 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1852, numericCheck1852, reducedZero1852 B hB hF, mul_zero]

theorem reducedZero1853 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1853 (mixedVector B) = 0 := by
  have h4239 : mixedVector B (Sum.inr 4239) = Sparse.eval nodeValue4239 (mixedVector B) := by
    change mixedMoment B node4239 node4239Labels = _
    exact sound4239 B hB hF
  have h4242 : mixedVector B (Sum.inr 4242) = Sparse.eval nodeValue4242 (mixedVector B) := by
    change mixedMoment B node4242 node4242Labels = _
    exact sound4242 B hB hF
  have h4279 : mixedVector B (Sum.inr 4279) = Sparse.eval nodeValue4279 (mixedVector B) := by
    change mixedMoment B node4279 node4279Labels = _
    exact sound4279 B hB hF
  have h4689 : mixedVector B (Sum.inr 4689) = Sparse.eval nodeValue4689 (mixedVector B) := by
    change mixedMoment B node4689 node4689Labels = _
    exact sound4689 B hB hF
  have h4692 : mixedVector B (Sum.inr 4692) = Sparse.eval nodeValue4692 (mixedVector B) := by
    change mixedMoment B node4692 node4692Labels = _
    exact sound4692 B hB hF
  have h4725 : mixedVector B (Sum.inr 4725) = Sparse.eval nodeValue4725 (mixedVector B) := by
    change mixedMoment B node4725 node4725Labels = _
    exact sound4725 B hB hF
  have h4726 : mixedVector B (Sum.inr 4726) = Sparse.eval nodeValue4726 (mixedVector B) := by
    change mixedMoment B node4726 node4726Labels = _
    exact sound4726 B hB hF
  have h4750 : mixedVector B (Sum.inr 4750) = Sparse.eval nodeValue4750 (mixedVector B) := by
    change mixedMoment B node4750 node4750Labels = _
    exact sound4750 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h5390 : mixedVector B (Sum.inr 5390) = Sparse.eval nodeValue5390 (mixedVector B) := by
    change mixedMoment B node5390 node5390Labels = _
    exact sound5390 B hB hF
  have h5404 : mixedVector B (Sum.inr 5404) = Sparse.eval nodeValue5404 (mixedVector B) := by
    change mixedMoment B node5404 node5404Labels = _
    exact sound5404 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  simpa only [sourceForm2266, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4239, h4242, h4279, h4689, h4692, h4725, h4726, h4750, h4866, h4868, h4896, h5390, h5404, h5451, reducedSource1853] using sourceEq2266 B hB

theorem rowSound1853 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1853 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1853, numericCheck1853, reducedZero1853 B hB hF, mul_zero]

theorem reducedZero1854 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1854 (mixedVector B) = 0 := by
  have h739 : mixedVector B (Sum.inr 739) = Sparse.eval nodeValue739 (mixedVector B) := by
    change mixedMoment B node739 node739Labels = _
    exact sound739 B hB hF
  have h742 : mixedVector B (Sum.inr 742) = Sparse.eval nodeValue742 (mixedVector B) := by
    change mixedMoment B node742 node742Labels = _
    exact sound742 B hB hF
  have h831 : mixedVector B (Sum.inr 831) = Sparse.eval nodeValue831 (mixedVector B) := by
    change mixedMoment B node831 node831Labels = _
    exact sound831 B hB hF
  have h1815 : mixedVector B (Sum.inr 1815) = Sparse.eval nodeValue1815 (mixedVector B) := by
    change mixedMoment B node1815 node1815Labels = _
    exact sound1815 B hB hF
  have h1818 : mixedVector B (Sum.inr 1818) = Sparse.eval nodeValue1818 (mixedVector B) := by
    change mixedMoment B node1818 node1818Labels = _
    exact sound1818 B hB hF
  have h1879 : mixedVector B (Sum.inr 1879) = Sparse.eval nodeValue1879 (mixedVector B) := by
    change mixedMoment B node1879 node1879Labels = _
    exact sound1879 B hB hF
  have h1880 : mixedVector B (Sum.inr 1880) = Sparse.eval nodeValue1880 (mixedVector B) := by
    change mixedMoment B node1880 node1880Labels = _
    exact sound1880 B hB hF
  have h1929 : mixedVector B (Sum.inr 1929) = Sparse.eval nodeValue1929 (mixedVector B) := by
    change mixedMoment B node1929 node1929Labels = _
    exact sound1929 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h3741 : mixedVector B (Sum.inr 3741) = Sparse.eval nodeValue3741 (mixedVector B) := by
    change mixedMoment B node3741 node3741Labels = _
    exact sound3741 B hB hF
  have h3790 : mixedVector B (Sum.inr 3790) = Sparse.eval nodeValue3790 (mixedVector B) := by
    change mixedMoment B node3790 node3790Labels = _
    exact sound3790 B hB hF
  have h3888 : mixedVector B (Sum.inr 3888) = Sparse.eval nodeValue3888 (mixedVector B) := by
    change mixedMoment B node3888 node3888Labels = _
    exact sound3888 B hB hF
  simpa only [sourceForm2267, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h739, h742, h831, h1815, h1818, h1879, h1880, h1929, h2107, h2109, h2278, h3741, h3790, h3888, reducedSource1854] using sourceEq2267 B hB

theorem rowSound1854 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1854 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1854, numericCheck1854, reducedZero1854 B hB hF, mul_zero]

theorem reducedZero1855 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1855 (mixedVector B) = 0 := by
  have h4487 : mixedVector B (Sum.inr 4487) = Sparse.eval nodeValue4487 (mixedVector B) := by
    change mixedMoment B node4487 node4487Labels = _
    exact sound4487 B hB hF
  have h4491 : mixedVector B (Sum.inr 4491) = Sparse.eval nodeValue4491 (mixedVector B) := by
    change mixedMoment B node4491 node4491Labels = _
    exact sound4491 B hB hF
  have h4506 : mixedVector B (Sum.inr 4506) = Sparse.eval nodeValue4506 (mixedVector B) := by
    change mixedMoment B node4506 node4506Labels = _
    exact sound4506 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4825 : mixedVector B (Sum.inr 4825) = Sparse.eval nodeValue4825 (mixedVector B) := by
    change mixedMoment B node4825 node4825Labels = _
    exact sound4825 B hB hF
  have h4828 : mixedVector B (Sum.inr 4828) = Sparse.eval nodeValue4828 (mixedVector B) := by
    change mixedMoment B node4828 node4828Labels = _
    exact sound4828 B hB hF
  have h4842 : mixedVector B (Sum.inr 4842) = Sparse.eval nodeValue4842 (mixedVector B) := by
    change mixedMoment B node4842 node4842Labels = _
    exact sound4842 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4856 : mixedVector B (Sum.inr 4856) = Sparse.eval nodeValue4856 (mixedVector B) := by
    change mixedMoment B node4856 node4856Labels = _
    exact sound4856 B hB hF
  have h4874 : mixedVector B (Sum.inr 4874) = Sparse.eval nodeValue4874 (mixedVector B) := by
    change mixedMoment B node4874 node4874Labels = _
    exact sound4874 B hB hF
  have h4884 : mixedVector B (Sum.inr 4884) = Sparse.eval nodeValue4884 (mixedVector B) := by
    change mixedMoment B node4884 node4884Labels = _
    exact sound4884 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5189 : mixedVector B (Sum.inr 5189) = Sparse.eval nodeValue5189 (mixedVector B) := by
    change mixedMoment B node5189 node5189Labels = _
    exact sound5189 B hB hF
  have h5207 : mixedVector B (Sum.inr 5207) = Sparse.eval nodeValue5207 (mixedVector B) := by
    change mixedMoment B node5207 node5207Labels = _
    exact sound5207 B hB hF
  simpa only [sourceForm2268, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4487, h4491, h4506, h4811, h4825, h4828, h4842, h4846, h4856, h4874, h4884, h5177, h5189, h5207, reducedSource1855] using sourceEq2268 B hB

theorem rowSound1855 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1855 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1855, numericCheck1855, reducedZero1855 B hB hF, mul_zero]

theorem sourceRowsAt1840 : MixedData.sourceRows (1840 : Fin 2425) =
    MixedData.row1840 := by decide +kernel

theorem sourceRowsAt1841 : MixedData.sourceRows (1841 : Fin 2425) =
    MixedData.row1841 := by decide +kernel

theorem sourceRowsAt1842 : MixedData.sourceRows (1842 : Fin 2425) =
    MixedData.row1842 := by decide +kernel

theorem sourceRowsAt1843 : MixedData.sourceRows (1843 : Fin 2425) =
    MixedData.row1843 := by decide +kernel

theorem sourceRowsAt1844 : MixedData.sourceRows (1844 : Fin 2425) =
    MixedData.row1844 := by decide +kernel

theorem sourceRowsAt1845 : MixedData.sourceRows (1845 : Fin 2425) =
    MixedData.row1845 := by decide +kernel

theorem sourceRowsAt1846 : MixedData.sourceRows (1846 : Fin 2425) =
    MixedData.row1846 := by decide +kernel

theorem sourceRowsAt1847 : MixedData.sourceRows (1847 : Fin 2425) =
    MixedData.row1847 := by decide +kernel

theorem sourceRowsAt1848 : MixedData.sourceRows (1848 : Fin 2425) =
    MixedData.row1848 := by decide +kernel

theorem sourceRowsAt1849 : MixedData.sourceRows (1849 : Fin 2425) =
    MixedData.row1849 := by decide +kernel

theorem sourceRowsAt1850 : MixedData.sourceRows (1850 : Fin 2425) =
    MixedData.row1850 := by decide +kernel

theorem sourceRowsAt1851 : MixedData.sourceRows (1851 : Fin 2425) =
    MixedData.row1851 := by decide +kernel

theorem sourceRowsAt1852 : MixedData.sourceRows (1852 : Fin 2425) =
    MixedData.row1852 := by decide +kernel

theorem sourceRowsAt1853 : MixedData.sourceRows (1853 : Fin 2425) =
    MixedData.row1853 := by decide +kernel

theorem sourceRowsAt1854 : MixedData.sourceRows (1854 : Fin 2425) =
    MixedData.row1854 := by decide +kernel

theorem sourceRowsAt1855 : MixedData.sourceRows (1855 : Fin 2425) =
    MixedData.row1855 := by decide +kernel

theorem chunkSound115 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 115) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1840 ∨ k.val = 1841 ∨ k.val = 1842 ∨ k.val = 1843 ∨ k.val = 1844 ∨ k.val = 1845 ∨ k.val = 1846 ∨ k.val = 1847 ∨ k.val = 1848 ∨ k.val = 1849 ∨ k.val = 1850 ∨ k.val = 1851 ∨ k.val = 1852 ∨ k.val = 1853 ∨ k.val = 1854 ∨ k.val = 1855 := by omega
  rcases heq with h1840 | h1841 | h1842 | h1843 | h1844 | h1845 | h1846 | h1847 | h1848 | h1849 | h1850 | h1851 | h1852 | h1853 | h1854 | h1855
  · have he : k = (1840 : Fin 2425) := Fin.ext h1840
    subst k
    rw [sourceRowsAt1840]
    exact rowSound1840 B hB hF
  · have he : k = (1841 : Fin 2425) := Fin.ext h1841
    subst k
    rw [sourceRowsAt1841]
    exact rowSound1841 B hB hF
  · have he : k = (1842 : Fin 2425) := Fin.ext h1842
    subst k
    rw [sourceRowsAt1842]
    exact rowSound1842 B hB hF
  · have he : k = (1843 : Fin 2425) := Fin.ext h1843
    subst k
    rw [sourceRowsAt1843]
    exact rowSound1843 B hB hF
  · have he : k = (1844 : Fin 2425) := Fin.ext h1844
    subst k
    rw [sourceRowsAt1844]
    exact rowSound1844 B hB hF
  · have he : k = (1845 : Fin 2425) := Fin.ext h1845
    subst k
    rw [sourceRowsAt1845]
    exact rowSound1845 B hB hF
  · have he : k = (1846 : Fin 2425) := Fin.ext h1846
    subst k
    rw [sourceRowsAt1846]
    exact rowSound1846 B hB hF
  · have he : k = (1847 : Fin 2425) := Fin.ext h1847
    subst k
    rw [sourceRowsAt1847]
    exact rowSound1847 B hB hF
  · have he : k = (1848 : Fin 2425) := Fin.ext h1848
    subst k
    rw [sourceRowsAt1848]
    exact rowSound1848 B hB hF
  · have he : k = (1849 : Fin 2425) := Fin.ext h1849
    subst k
    rw [sourceRowsAt1849]
    exact rowSound1849 B hB hF
  · have he : k = (1850 : Fin 2425) := Fin.ext h1850
    subst k
    rw [sourceRowsAt1850]
    exact rowSound1850 B hB hF
  · have he : k = (1851 : Fin 2425) := Fin.ext h1851
    subst k
    rw [sourceRowsAt1851]
    exact rowSound1851 B hB hF
  · have he : k = (1852 : Fin 2425) := Fin.ext h1852
    subst k
    rw [sourceRowsAt1852]
    exact rowSound1852 B hB hF
  · have he : k = (1853 : Fin 2425) := Fin.ext h1853
    subst k
    rw [sourceRowsAt1853]
    exact rowSound1853 B hB hF
  · have he : k = (1854 : Fin 2425) := Fin.ext h1854
    subst k
    rw [sourceRowsAt1854]
    exact rowSound1854 B hB hF
  · have he : k = (1855 : Fin 2425) := Fin.ext h1855
    subst k
    rw [sourceRowsAt1855]
    exact rowSound1855 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
