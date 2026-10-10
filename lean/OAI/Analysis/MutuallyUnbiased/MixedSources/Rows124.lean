import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic124
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources77

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1984 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1984 (mixedVector B) = 0 := by
  have h4327 : mixedVector B (Sum.inr 4327) = Sparse.eval nodeValue4327 (mixedVector B) := by
    change mixedMoment B node4327 node4327Labels = _
    exact sound4327 B hB hF
  have h4329 : mixedVector B (Sum.inr 4329) = Sparse.eval nodeValue4329 (mixedVector B) := by
    change mixedMoment B node4329 node4329Labels = _
    exact sound4329 B hB hF
  have h4332 : mixedVector B (Sum.inr 4332) = Sparse.eval nodeValue4332 (mixedVector B) := by
    change mixedMoment B node4332 node4332Labels = _
    exact sound4332 B hB hF
  have h4344 : mixedVector B (Sum.inr 4344) = Sparse.eval nodeValue4344 (mixedVector B) := by
    change mixedMoment B node4344 node4344Labels = _
    exact sound4344 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4664 : mixedVector B (Sum.inr 4664) = Sparse.eval nodeValue4664 (mixedVector B) := by
    change mixedMoment B node4664 node4664Labels = _
    exact sound4664 B hB hF
  have h4666 : mixedVector B (Sum.inr 4666) = Sparse.eval nodeValue4666 (mixedVector B) := by
    change mixedMoment B node4666 node4666Labels = _
    exact sound4666 B hB hF
  have h4668 : mixedVector B (Sum.inr 4668) = Sparse.eval nodeValue4668 (mixedVector B) := by
    change mixedMoment B node4668 node4668Labels = _
    exact sound4668 B hB hF
  have h4679 : mixedVector B (Sum.inr 4679) = Sparse.eval nodeValue4679 (mixedVector B) := by
    change mixedMoment B node4679 node4679Labels = _
    exact sound4679 B hB hF
  have h4772 : mixedVector B (Sum.inr 4772) = Sparse.eval nodeValue4772 (mixedVector B) := by
    change mixedMoment B node4772 node4772Labels = _
    exact sound4772 B hB hF
  have h4774 : mixedVector B (Sum.inr 4774) = Sparse.eval nodeValue4774 (mixedVector B) := by
    change mixedMoment B node4774 node4774Labels = _
    exact sound4774 B hB hF
  have h4775 : mixedVector B (Sum.inr 4775) = Sparse.eval nodeValue4775 (mixedVector B) := by
    change mixedMoment B node4775 node4775Labels = _
    exact sound4775 B hB hF
  have h4792 : mixedVector B (Sum.inr 4792) = Sparse.eval nodeValue4792 (mixedVector B) := by
    change mixedMoment B node4792 node4792Labels = _
    exact sound4792 B hB hF
  have h4795 : mixedVector B (Sum.inr 4795) = Sparse.eval nodeValue4795 (mixedVector B) := by
    change mixedMoment B node4795 node4795Labels = _
    exact sound4795 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4833 : mixedVector B (Sum.inr 4833) = Sparse.eval nodeValue4833 (mixedVector B) := by
    change mixedMoment B node4833 node4833Labels = _
    exact sound4833 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4893 : mixedVector B (Sum.inr 4893) = Sparse.eval nodeValue4893 (mixedVector B) := by
    change mixedMoment B node4893 node4893Labels = _
    exact sound4893 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h5226 : mixedVector B (Sum.inr 5226) = Sparse.eval nodeValue5226 (mixedVector B) := by
    change mixedMoment B node5226 node5226Labels = _
    exact sound5226 B hB hF
  have h5255 : mixedVector B (Sum.inr 5255) = Sparse.eval nodeValue5255 (mixedVector B) := by
    change mixedMoment B node5255 node5255Labels = _
    exact sound5255 B hB hF
  have h5256 : mixedVector B (Sum.inr 5256) = Sparse.eval nodeValue5256 (mixedVector B) := by
    change mixedMoment B node5256 node5256Labels = _
    exact sound5256 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  simpa only [sourceForm2466, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4327, h4329, h4332, h4344, h4458, h4664, h4666, h4668, h4679, h4772, h4774, h4775, h4792, h4795, h4802, h4805, h4807, h4811, h4833, h4838, h4866, h4888, h4893, h4895, h5226, h5255, h5256, h5257, h5271, reducedSource1984] using sourceEq2466 B hB

theorem rowSound1984 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1984 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1984, numericCheck1984, reducedZero1984 B hB hF, mul_zero]

theorem reducedZero1985 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1985 (mixedVector B) = 0 := by
  have h1327 : mixedVector B (Sum.inr 1327) = Sparse.eval nodeValue1327 (mixedVector B) := by
    change mixedMoment B node1327 node1327Labels = _
    exact sound1327 B hB hF
  have h1328 : mixedVector B (Sum.inr 1328) = Sparse.eval nodeValue1328 (mixedVector B) := by
    change mixedMoment B node1328 node1328Labels = _
    exact sound1328 B hB hF
  have h1331 : mixedVector B (Sum.inr 1331) = Sparse.eval nodeValue1331 (mixedVector B) := by
    change mixedMoment B node1331 node1331Labels = _
    exact sound1331 B hB hF
  have h1339 : mixedVector B (Sum.inr 1339) = Sparse.eval nodeValue1339 (mixedVector B) := by
    change mixedMoment B node1339 node1339Labels = _
    exact sound1339 B hB hF
  have h1411 : mixedVector B (Sum.inr 1411) = Sparse.eval nodeValue1411 (mixedVector B) := by
    change mixedMoment B node1411 node1411Labels = _
    exact sound1411 B hB hF
  have h2423 : mixedVector B (Sum.inr 2423) = Sparse.eval nodeValue2423 (mixedVector B) := by
    change mixedMoment B node2423 node2423Labels = _
    exact sound2423 B hB hF
  have h2430 : mixedVector B (Sum.inr 2430) = Sparse.eval nodeValue2430 (mixedVector B) := by
    change mixedMoment B node2430 node2430Labels = _
    exact sound2430 B hB hF
  have h2471 : mixedVector B (Sum.inr 2471) = Sparse.eval nodeValue2471 (mixedVector B) := by
    change mixedMoment B node2471 node2471Labels = _
    exact sound2471 B hB hF
  have h2574 : mixedVector B (Sum.inr 2574) = Sparse.eval nodeValue2574 (mixedVector B) := by
    change mixedMoment B node2574 node2574Labels = _
    exact sound2574 B hB hF
  have h3084 : mixedVector B (Sum.inr 3084) = Sparse.eval nodeValue3084 (mixedVector B) := by
    change mixedMoment B node3084 node3084Labels = _
    exact sound3084 B hB hF
  have h3085 : mixedVector B (Sum.inr 3085) = Sparse.eval nodeValue3085 (mixedVector B) := by
    change mixedMoment B node3085 node3085Labels = _
    exact sound3085 B hB hF
  have h3087 : mixedVector B (Sum.inr 3087) = Sparse.eval nodeValue3087 (mixedVector B) := by
    change mixedMoment B node3087 node3087Labels = _
    exact sound3087 B hB hF
  have h3091 : mixedVector B (Sum.inr 3091) = Sparse.eval nodeValue3091 (mixedVector B) := by
    change mixedMoment B node3091 node3091Labels = _
    exact sound3091 B hB hF
  have h3109 : mixedVector B (Sum.inr 3109) = Sparse.eval nodeValue3109 (mixedVector B) := by
    change mixedMoment B node3109 node3109Labels = _
    exact sound3109 B hB hF
  have h3133 : mixedVector B (Sum.inr 3133) = Sparse.eval nodeValue3133 (mixedVector B) := by
    change mixedMoment B node3133 node3133Labels = _
    exact sound3133 B hB hF
  have h3135 : mixedVector B (Sum.inr 3135) = Sparse.eval nodeValue3135 (mixedVector B) := by
    change mixedMoment B node3135 node3135Labels = _
    exact sound3135 B hB hF
  have h3139 : mixedVector B (Sum.inr 3139) = Sparse.eval nodeValue3139 (mixedVector B) := by
    change mixedMoment B node3139 node3139Labels = _
    exact sound3139 B hB hF
  have h3162 : mixedVector B (Sum.inr 3162) = Sparse.eval nodeValue3162 (mixedVector B) := by
    change mixedMoment B node3162 node3162Labels = _
    exact sound3162 B hB hF
  have h3164 : mixedVector B (Sum.inr 3164) = Sparse.eval nodeValue3164 (mixedVector B) := by
    change mixedMoment B node3164 node3164Labels = _
    exact sound3164 B hB hF
  have h3184 : mixedVector B (Sum.inr 3184) = Sparse.eval nodeValue3184 (mixedVector B) := by
    change mixedMoment B node3184 node3184Labels = _
    exact sound3184 B hB hF
  have h3199 : mixedVector B (Sum.inr 3199) = Sparse.eval nodeValue3199 (mixedVector B) := by
    change mixedMoment B node3199 node3199Labels = _
    exact sound3199 B hB hF
  have h3203 : mixedVector B (Sum.inr 3203) = Sparse.eval nodeValue3203 (mixedVector B) := by
    change mixedMoment B node3203 node3203Labels = _
    exact sound3203 B hB hF
  have h3204 : mixedVector B (Sum.inr 3204) = Sparse.eval nodeValue3204 (mixedVector B) := by
    change mixedMoment B node3204 node3204Labels = _
    exact sound3204 B hB hF
  have h3207 : mixedVector B (Sum.inr 3207) = Sparse.eval nodeValue3207 (mixedVector B) := by
    change mixedMoment B node3207 node3207Labels = _
    exact sound3207 B hB hF
  have h3212 : mixedVector B (Sum.inr 3212) = Sparse.eval nodeValue3212 (mixedVector B) := by
    change mixedMoment B node3212 node3212Labels = _
    exact sound3212 B hB hF
  have h3213 : mixedVector B (Sum.inr 3213) = Sparse.eval nodeValue3213 (mixedVector B) := by
    change mixedMoment B node3213 node3213Labels = _
    exact sound3213 B hB hF
  have h3227 : mixedVector B (Sum.inr 3227) = Sparse.eval nodeValue3227 (mixedVector B) := by
    change mixedMoment B node3227 node3227Labels = _
    exact sound3227 B hB hF
  have h3228 : mixedVector B (Sum.inr 3228) = Sparse.eval nodeValue3228 (mixedVector B) := by
    change mixedMoment B node3228 node3228Labels = _
    exact sound3228 B hB hF
  have h3229 : mixedVector B (Sum.inr 3229) = Sparse.eval nodeValue3229 (mixedVector B) := by
    change mixedMoment B node3229 node3229Labels = _
    exact sound3229 B hB hF
  simpa only [sourceForm2467, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1327, h1328, h1331, h1339, h1411, h2423, h2430, h2471, h2574, h3084, h3085, h3087, h3091, h3109, h3133, h3135, h3139, h3162, h3164, h3184, h3199, h3203, h3204, h3207, h3212, h3213, h3227, h3228, h3229, reducedSource1985] using sourceEq2467 B hB

theorem rowSound1985 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1985 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1985, numericCheck1985, reducedZero1985 B hB hF, mul_zero]

theorem reducedZero1986 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1986 (mixedVector B) = 0 := by
  have h1670 : mixedVector B (Sum.inr 1670) = Sparse.eval nodeValue1670 (mixedVector B) := by
    change mixedMoment B node1670 node1670Labels = _
    exact sound1670 B hB hF
  have h1671 : mixedVector B (Sum.inr 1671) = Sparse.eval nodeValue1671 (mixedVector B) := by
    change mixedMoment B node1671 node1671Labels = _
    exact sound1671 B hB hF
  have h1673 : mixedVector B (Sum.inr 1673) = Sparse.eval nodeValue1673 (mixedVector B) := by
    change mixedMoment B node1673 node1673Labels = _
    exact sound1673 B hB hF
  have h1678 : mixedVector B (Sum.inr 1678) = Sparse.eval nodeValue1678 (mixedVector B) := by
    change mixedMoment B node1678 node1678Labels = _
    exact sound1678 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h2147 : mixedVector B (Sum.inr 2147) = Sparse.eval nodeValue2147 (mixedVector B) := by
    change mixedMoment B node2147 node2147Labels = _
    exact sound2147 B hB hF
  have h2148 : mixedVector B (Sum.inr 2148) = Sparse.eval nodeValue2148 (mixedVector B) := by
    change mixedMoment B node2148 node2148Labels = _
    exact sound2148 B hB hF
  have h2150 : mixedVector B (Sum.inr 2150) = Sparse.eval nodeValue2150 (mixedVector B) := by
    change mixedMoment B node2150 node2150Labels = _
    exact sound2150 B hB hF
  have h2154 : mixedVector B (Sum.inr 2154) = Sparse.eval nodeValue2154 (mixedVector B) := by
    change mixedMoment B node2154 node2154Labels = _
    exact sound2154 B hB hF
  have h2198 : mixedVector B (Sum.inr 2198) = Sparse.eval nodeValue2198 (mixedVector B) := by
    change mixedMoment B node2198 node2198Labels = _
    exact sound2198 B hB hF
  have h2199 : mixedVector B (Sum.inr 2199) = Sparse.eval nodeValue2199 (mixedVector B) := by
    change mixedMoment B node2199 node2199Labels = _
    exact sound2199 B hB hF
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2204 : mixedVector B (Sum.inr 2204) = Sparse.eval nodeValue2204 (mixedVector B) := by
    change mixedMoment B node2204 node2204Labels = _
    exact sound2204 B hB hF
  have h2211 : mixedVector B (Sum.inr 2211) = Sparse.eval nodeValue2211 (mixedVector B) := by
    change mixedMoment B node2211 node2211Labels = _
    exact sound2211 B hB hF
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h2214 : mixedVector B (Sum.inr 2214) = Sparse.eval nodeValue2214 (mixedVector B) := by
    change mixedMoment B node2214 node2214Labels = _
    exact sound2214 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2227 : mixedVector B (Sum.inr 2227) = Sparse.eval nodeValue2227 (mixedVector B) := by
    change mixedMoment B node2227 node2227Labels = _
    exact sound2227 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2718 : mixedVector B (Sum.inr 2718) = Sparse.eval nodeValue2718 (mixedVector B) := by
    change mixedMoment B node2718 node2718Labels = _
    exact sound2718 B hB hF
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  simpa only [sourceForm2468, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1670, h1671, h1673, h1678, h1724, h2147, h2148, h2150, h2154, h2198, h2199, h2201, h2202, h2204, h2211, h2213, h2214, h2224, h2225, h2227, h2260, h2262, h2263, h2291, h2669, h2718, h2720, h2721, h2739, reducedSource1986] using sourceEq2468 B hB

theorem rowSound1986 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1986 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1986, numericCheck1986, reducedZero1986 B hB hF, mul_zero]

theorem reducedZero1987 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1987 (mixedVector B) = 0 := by
  have h1790 : mixedVector B (Sum.inr 1790) = Sparse.eval nodeValue1790 (mixedVector B) := by
    change mixedMoment B node1790 node1790Labels = _
    exact sound1790 B hB hF
  have h1792 : mixedVector B (Sum.inr 1792) = Sparse.eval nodeValue1792 (mixedVector B) := by
    change mixedMoment B node1792 node1792Labels = _
    exact sound1792 B hB hF
  have h1794 : mixedVector B (Sum.inr 1794) = Sparse.eval nodeValue1794 (mixedVector B) := by
    change mixedMoment B node1794 node1794Labels = _
    exact sound1794 B hB hF
  have h1805 : mixedVector B (Sum.inr 1805) = Sparse.eval nodeValue1805 (mixedVector B) := by
    change mixedMoment B node1805 node1805Labels = _
    exact sound1805 B hB hF
  have h2020 : mixedVector B (Sum.inr 2020) = Sparse.eval nodeValue2020 (mixedVector B) := by
    change mixedMoment B node2020 node2020Labels = _
    exact sound2020 B hB hF
  have h3376 : mixedVector B (Sum.inr 3376) = Sparse.eval nodeValue3376 (mixedVector B) := by
    change mixedMoment B node3376 node3376Labels = _
    exact sound3376 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2469, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1790, h1792, h1794, h1805, h2020, h3376, h4083, reducedSource1987] using sourceEq2469 B hB

theorem rowSound1987 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1987 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1987, numericCheck1987, reducedZero1987 B hB hF, mul_zero]

theorem reducedZero1988 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1988 (mixedVector B) = 0 := by
  have h4196 : mixedVector B (Sum.inr 4196) = Sparse.eval nodeValue4196 (mixedVector B) := by
    change mixedMoment B node4196 node4196Labels = _
    exact sound4196 B hB hF
  have h4197 : mixedVector B (Sum.inr 4197) = Sparse.eval nodeValue4197 (mixedVector B) := by
    change mixedMoment B node4197 node4197Labels = _
    exact sound4197 B hB hF
  have h4201 : mixedVector B (Sum.inr 4201) = Sparse.eval nodeValue4201 (mixedVector B) := by
    change mixedMoment B node4201 node4201Labels = _
    exact sound4201 B hB hF
  have h4210 : mixedVector B (Sum.inr 4210) = Sparse.eval nodeValue4210 (mixedVector B) := by
    change mixedMoment B node4210 node4210Labels = _
    exact sound4210 B hB hF
  have h4249 : mixedVector B (Sum.inr 4249) = Sparse.eval nodeValue4249 (mixedVector B) := by
    change mixedMoment B node4249 node4249Labels = _
    exact sound4249 B hB hF
  have h4631 : mixedVector B (Sum.inr 4631) = Sparse.eval nodeValue4631 (mixedVector B) := by
    change mixedMoment B node4631 node4631Labels = _
    exact sound4631 B hB hF
  have h4632 : mixedVector B (Sum.inr 4632) = Sparse.eval nodeValue4632 (mixedVector B) := by
    change mixedMoment B node4632 node4632Labels = _
    exact sound4632 B hB hF
  have h4635 : mixedVector B (Sum.inr 4635) = Sparse.eval nodeValue4635 (mixedVector B) := by
    change mixedMoment B node4635 node4635Labels = _
    exact sound4635 B hB hF
  have h4642 : mixedVector B (Sum.inr 4642) = Sparse.eval nodeValue4642 (mixedVector B) := by
    change mixedMoment B node4642 node4642Labels = _
    exact sound4642 B hB hF
  have h4760 : mixedVector B (Sum.inr 4760) = Sparse.eval nodeValue4760 (mixedVector B) := by
    change mixedMoment B node4760 node4760Labels = _
    exact sound4760 B hB hF
  have h4763 : mixedVector B (Sum.inr 4763) = Sparse.eval nodeValue4763 (mixedVector B) := by
    change mixedMoment B node4763 node4763Labels = _
    exact sound4763 B hB hF
  have h4767 : mixedVector B (Sum.inr 4767) = Sparse.eval nodeValue4767 (mixedVector B) := by
    change mixedMoment B node4767 node4767Labels = _
    exact sound4767 B hB hF
  have h4779 : mixedVector B (Sum.inr 4779) = Sparse.eval nodeValue4779 (mixedVector B) := by
    change mixedMoment B node4779 node4779Labels = _
    exact sound4779 B hB hF
  have h4782 : mixedVector B (Sum.inr 4782) = Sparse.eval nodeValue4782 (mixedVector B) := by
    change mixedMoment B node4782 node4782Labels = _
    exact sound4782 B hB hF
  have h4787 : mixedVector B (Sum.inr 4787) = Sparse.eval nodeValue4787 (mixedVector B) := by
    change mixedMoment B node4787 node4787Labels = _
    exact sound4787 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4887 : mixedVector B (Sum.inr 4887) = Sparse.eval nodeValue4887 (mixedVector B) := by
    change mixedMoment B node4887 node4887Labels = _
    exact sound4887 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h5352 : mixedVector B (Sum.inr 5352) = Sparse.eval nodeValue5352 (mixedVector B) := by
    change mixedMoment B node5352 node5352Labels = _
    exact sound5352 B hB hF
  have h5416 : mixedVector B (Sum.inr 5416) = Sparse.eval nodeValue5416 (mixedVector B) := by
    change mixedMoment B node5416 node5416Labels = _
    exact sound5416 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  simpa only [sourceForm2470, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4196, h4197, h4201, h4210, h4249, h4631, h4632, h4635, h4642, h4760, h4763, h4767, h4779, h4782, h4787, h4801, h4802, h4804, h4811, h4831, h4835, h4887, h4888, h5352, h5416, h5424, h5433, h5434, reducedSource1988] using sourceEq2470 B hB

theorem rowSound1988 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1988 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1988, numericCheck1988, reducedZero1988 B hB hF, mul_zero]

theorem reducedZero1989 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1989 (mixedVector B) = 0 := by
  have h4396 : mixedVector B (Sum.inr 4396) = Sparse.eval nodeValue4396 (mixedVector B) := by
    change mixedMoment B node4396 node4396Labels = _
    exact sound4396 B hB hF
  have h4397 : mixedVector B (Sum.inr 4397) = Sparse.eval nodeValue4397 (mixedVector B) := by
    change mixedMoment B node4397 node4397Labels = _
    exact sound4397 B hB hF
  have h4400 : mixedVector B (Sum.inr 4400) = Sparse.eval nodeValue4400 (mixedVector B) := by
    change mixedMoment B node4400 node4400Labels = _
    exact sound4400 B hB hF
  have h4417 : mixedVector B (Sum.inr 4417) = Sparse.eval nodeValue4417 (mixedVector B) := by
    change mixedMoment B node4417 node4417Labels = _
    exact sound4417 B hB hF
  have h4449 : mixedVector B (Sum.inr 4449) = Sparse.eval nodeValue4449 (mixedVector B) := by
    change mixedMoment B node4449 node4449Labels = _
    exact sound4449 B hB hF
  have h4736 : mixedVector B (Sum.inr 4736) = Sparse.eval nodeValue4736 (mixedVector B) := by
    change mixedMoment B node4736 node4736Labels = _
    exact sound4736 B hB hF
  have h4737 : mixedVector B (Sum.inr 4737) = Sparse.eval nodeValue4737 (mixedVector B) := by
    change mixedMoment B node4737 node4737Labels = _
    exact sound4737 B hB hF
  have h4739 : mixedVector B (Sum.inr 4739) = Sparse.eval nodeValue4739 (mixedVector B) := by
    change mixedMoment B node4739 node4739Labels = _
    exact sound4739 B hB hF
  have h4740 : mixedVector B (Sum.inr 4740) = Sparse.eval nodeValue4740 (mixedVector B) := by
    change mixedMoment B node4740 node4740Labels = _
    exact sound4740 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4799 : mixedVector B (Sum.inr 4799) = Sparse.eval nodeValue4799 (mixedVector B) := by
    change mixedMoment B node4799 node4799Labels = _
    exact sound4799 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4803 : mixedVector B (Sum.inr 4803) = Sparse.eval nodeValue4803 (mixedVector B) := by
    change mixedMoment B node4803 node4803Labels = _
    exact sound4803 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4813 : mixedVector B (Sum.inr 4813) = Sparse.eval nodeValue4813 (mixedVector B) := by
    change mixedMoment B node4813 node4813Labels = _
    exact sound4813 B hB hF
  have h4815 : mixedVector B (Sum.inr 4815) = Sparse.eval nodeValue4815 (mixedVector B) := by
    change mixedMoment B node4815 node4815Labels = _
    exact sound4815 B hB hF
  have h4816 : mixedVector B (Sum.inr 4816) = Sparse.eval nodeValue4816 (mixedVector B) := by
    change mixedMoment B node4816 node4816Labels = _
    exact sound4816 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4849 : mixedVector B (Sum.inr 4849) = Sparse.eval nodeValue4849 (mixedVector B) := by
    change mixedMoment B node4849 node4849Labels = _
    exact sound4849 B hB hF
  have h4851 : mixedVector B (Sum.inr 4851) = Sparse.eval nodeValue4851 (mixedVector B) := by
    change mixedMoment B node4851 node4851Labels = _
    exact sound4851 B hB hF
  have h4852 : mixedVector B (Sum.inr 4852) = Sparse.eval nodeValue4852 (mixedVector B) := by
    change mixedMoment B node4852 node4852Labels = _
    exact sound4852 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5145 : mixedVector B (Sum.inr 5145) = Sparse.eval nodeValue5145 (mixedVector B) := by
    change mixedMoment B node5145 node5145Labels = _
    exact sound5145 B hB hF
  have h5148 : mixedVector B (Sum.inr 5148) = Sparse.eval nodeValue5148 (mixedVector B) := by
    change mixedMoment B node5148 node5148Labels = _
    exact sound5148 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  simpa only [sourceForm2471, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4396, h4397, h4400, h4417, h4449, h4736, h4737, h4739, h4740, h4798, h4799, h4801, h4802, h4803, h4805, h4813, h4815, h4816, h4834, h4835, h4838, h4849, h4851, h4852, h4866, h5073, h5145, h5148, h5149, h5169, reducedSource1989] using sourceEq2471 B hB

theorem rowSound1989 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1989 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1989, numericCheck1989, reducedZero1989 B hB hF, mul_zero]

theorem reducedZero1990 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1990 (mixedVector B) = 0 := by
  have h4326 : mixedVector B (Sum.inr 4326) = Sparse.eval nodeValue4326 (mixedVector B) := by
    change mixedMoment B node4326 node4326Labels = _
    exact sound4326 B hB hF
  have h4328 : mixedVector B (Sum.inr 4328) = Sparse.eval nodeValue4328 (mixedVector B) := by
    change mixedMoment B node4328 node4328Labels = _
    exact sound4328 B hB hF
  have h4341 : mixedVector B (Sum.inr 4341) = Sparse.eval nodeValue4341 (mixedVector B) := by
    change mixedMoment B node4341 node4341Labels = _
    exact sound4341 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4663 : mixedVector B (Sum.inr 4663) = Sparse.eval nodeValue4663 (mixedVector B) := by
    change mixedMoment B node4663 node4663Labels = _
    exact sound4663 B hB hF
  have h4665 : mixedVector B (Sum.inr 4665) = Sparse.eval nodeValue4665 (mixedVector B) := by
    change mixedMoment B node4665 node4665Labels = _
    exact sound4665 B hB hF
  have h4676 : mixedVector B (Sum.inr 4676) = Sparse.eval nodeValue4676 (mixedVector B) := by
    change mixedMoment B node4676 node4676Labels = _
    exact sound4676 B hB hF
  have h4771 : mixedVector B (Sum.inr 4771) = Sparse.eval nodeValue4771 (mixedVector B) := by
    change mixedMoment B node4771 node4771Labels = _
    exact sound4771 B hB hF
  have h4773 : mixedVector B (Sum.inr 4773) = Sparse.eval nodeValue4773 (mixedVector B) := by
    change mixedMoment B node4773 node4773Labels = _
    exact sound4773 B hB hF
  have h4803 : mixedVector B (Sum.inr 4803) = Sparse.eval nodeValue4803 (mixedVector B) := by
    change mixedMoment B node4803 node4803Labels = _
    exact sound4803 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  have h5219 : mixedVector B (Sum.inr 5219) = Sparse.eval nodeValue5219 (mixedVector B) := by
    change mixedMoment B node5219 node5219Labels = _
    exact sound5219 B hB hF
  have h5249 : mixedVector B (Sum.inr 5249) = Sparse.eval nodeValue5249 (mixedVector B) := by
    change mixedMoment B node5249 node5249Labels = _
    exact sound5249 B hB hF
  have h5250 : mixedVector B (Sum.inr 5250) = Sparse.eval nodeValue5250 (mixedVector B) := by
    change mixedMoment B node5250 node5250Labels = _
    exact sound5250 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  simpa only [sourceForm2472, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4326, h4328, h4341, h4457, h4663, h4665, h4676, h4771, h4773, h4803, h4804, h4810, h4831, h4834, h4865, h4888, h4894, h5219, h5249, h5250, h5258, reducedSource1990] using sourceEq2472 B hB

theorem rowSound1990 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1990 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1990, numericCheck1990, reducedZero1990 B hB hF, mul_zero]

theorem reducedZero1991 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1991 (mixedVector B) = 0 := by
  have h1329 : mixedVector B (Sum.inr 1329) = Sparse.eval nodeValue1329 (mixedVector B) := by
    change mixedMoment B node1329 node1329Labels = _
    exact sound1329 B hB hF
  have h1330 : mixedVector B (Sum.inr 1330) = Sparse.eval nodeValue1330 (mixedVector B) := by
    change mixedMoment B node1330 node1330Labels = _
    exact sound1330 B hB hF
  have h1341 : mixedVector B (Sum.inr 1341) = Sparse.eval nodeValue1341 (mixedVector B) := by
    change mixedMoment B node1341 node1341Labels = _
    exact sound1341 B hB hF
  have h1414 : mixedVector B (Sum.inr 1414) = Sparse.eval nodeValue1414 (mixedVector B) := by
    change mixedMoment B node1414 node1414Labels = _
    exact sound1414 B hB hF
  have h2890 : mixedVector B (Sum.inr 2890) = Sparse.eval nodeValue2890 (mixedVector B) := by
    change mixedMoment B node2890 node2890Labels = _
    exact sound2890 B hB hF
  have h2895 : mixedVector B (Sum.inr 2895) = Sparse.eval nodeValue2895 (mixedVector B) := by
    change mixedMoment B node2895 node2895Labels = _
    exact sound2895 B hB hF
  have h2941 : mixedVector B (Sum.inr 2941) = Sparse.eval nodeValue2941 (mixedVector B) := by
    change mixedMoment B node2941 node2941Labels = _
    exact sound2941 B hB hF
  have h3065 : mixedVector B (Sum.inr 3065) = Sparse.eval nodeValue3065 (mixedVector B) := by
    change mixedMoment B node3065 node3065Labels = _
    exact sound3065 B hB hF
  have h3066 : mixedVector B (Sum.inr 3066) = Sparse.eval nodeValue3066 (mixedVector B) := by
    change mixedMoment B node3066 node3066Labels = _
    exact sound3066 B hB hF
  have h3069 : mixedVector B (Sum.inr 3069) = Sparse.eval nodeValue3069 (mixedVector B) := by
    change mixedMoment B node3069 node3069Labels = _
    exact sound3069 B hB hF
  have h3089 : mixedVector B (Sum.inr 3089) = Sparse.eval nodeValue3089 (mixedVector B) := by
    change mixedMoment B node3089 node3089Labels = _
    exact sound3089 B hB hF
  have h3134 : mixedVector B (Sum.inr 3134) = Sparse.eval nodeValue3134 (mixedVector B) := by
    change mixedMoment B node3134 node3134Labels = _
    exact sound3134 B hB hF
  have h3140 : mixedVector B (Sum.inr 3140) = Sparse.eval nodeValue3140 (mixedVector B) := by
    change mixedMoment B node3140 node3140Labels = _
    exact sound3140 B hB hF
  have h3163 : mixedVector B (Sum.inr 3163) = Sparse.eval nodeValue3163 (mixedVector B) := by
    change mixedMoment B node3163 node3163Labels = _
    exact sound3163 B hB hF
  have h3185 : mixedVector B (Sum.inr 3185) = Sparse.eval nodeValue3185 (mixedVector B) := by
    change mixedMoment B node3185 node3185Labels = _
    exact sound3185 B hB hF
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3206 : mixedVector B (Sum.inr 3206) = Sparse.eval nodeValue3206 (mixedVector B) := by
    change mixedMoment B node3206 node3206Labels = _
    exact sound3206 B hB hF
  have h3209 : mixedVector B (Sum.inr 3209) = Sparse.eval nodeValue3209 (mixedVector B) := by
    change mixedMoment B node3209 node3209Labels = _
    exact sound3209 B hB hF
  have h3214 : mixedVector B (Sum.inr 3214) = Sparse.eval nodeValue3214 (mixedVector B) := by
    change mixedMoment B node3214 node3214Labels = _
    exact sound3214 B hB hF
  have h3227 : mixedVector B (Sum.inr 3227) = Sparse.eval nodeValue3227 (mixedVector B) := by
    change mixedMoment B node3227 node3227Labels = _
    exact sound3227 B hB hF
  have h3230 : mixedVector B (Sum.inr 3230) = Sparse.eval nodeValue3230 (mixedVector B) := by
    change mixedMoment B node3230 node3230Labels = _
    exact sound3230 B hB hF
  simpa only [sourceForm2473, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1329, h1330, h1341, h1414, h2890, h2895, h2941, h3065, h3066, h3069, h3089, h3134, h3140, h3163, h3185, h3202, h3206, h3209, h3214, h3227, h3230, reducedSource1991] using sourceEq2473 B hB

theorem rowSound1991 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1991 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1991, numericCheck1991, reducedZero1991 B hB hF, mul_zero]

theorem reducedZero1992 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1992 (mixedVector B) = 0 := by
  have h1663 : mixedVector B (Sum.inr 1663) = Sparse.eval nodeValue1663 (mixedVector B) := by
    change mixedMoment B node1663 node1663Labels = _
    exact sound1663 B hB hF
  have h1664 : mixedVector B (Sum.inr 1664) = Sparse.eval nodeValue1664 (mixedVector B) := by
    change mixedMoment B node1664 node1664Labels = _
    exact sound1664 B hB hF
  have h1667 : mixedVector B (Sum.inr 1667) = Sparse.eval nodeValue1667 (mixedVector B) := by
    change mixedMoment B node1667 node1667Labels = _
    exact sound1667 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h2140 : mixedVector B (Sum.inr 2140) = Sparse.eval nodeValue2140 (mixedVector B) := by
    change mixedMoment B node2140 node2140Labels = _
    exact sound2140 B hB hF
  have h2141 : mixedVector B (Sum.inr 2141) = Sparse.eval nodeValue2141 (mixedVector B) := by
    change mixedMoment B node2141 node2141Labels = _
    exact sound2141 B hB hF
  have h2144 : mixedVector B (Sum.inr 2144) = Sparse.eval nodeValue2144 (mixedVector B) := by
    change mixedMoment B node2144 node2144Labels = _
    exact sound2144 B hB hF
  have h2189 : mixedVector B (Sum.inr 2189) = Sparse.eval nodeValue2189 (mixedVector B) := by
    change mixedMoment B node2189 node2189Labels = _
    exact sound2189 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
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
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2661 : mixedVector B (Sum.inr 2661) = Sparse.eval nodeValue2661 (mixedVector B) := by
    change mixedMoment B node2661 node2661Labels = _
    exact sound2661 B hB hF
  have h2708 : mixedVector B (Sum.inr 2708) = Sparse.eval nodeValue2708 (mixedVector B) := by
    change mixedMoment B node2708 node2708Labels = _
    exact sound2708 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  simpa only [sourceForm2474, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1663, h1664, h1667, h1707, h2140, h2141, h2144, h2189, h2191, h2194, h2195, h2203, h2205, h2215, h2242, h2244, h2264, h2661, h2708, h2709, h2722, reducedSource1992] using sourceEq2474 B hB

theorem rowSound1992 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1992 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1992, numericCheck1992, reducedZero1992 B hB hF, mul_zero]

theorem reducedZero1993 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1993 (mixedVector B) = 0 := by
  have h4195 : mixedVector B (Sum.inr 4195) = Sparse.eval nodeValue4195 (mixedVector B) := by
    change mixedMoment B node4195 node4195Labels = _
    exact sound4195 B hB hF
  have h4197 : mixedVector B (Sum.inr 4197) = Sparse.eval nodeValue4197 (mixedVector B) := by
    change mixedMoment B node4197 node4197Labels = _
    exact sound4197 B hB hF
  have h4207 : mixedVector B (Sum.inr 4207) = Sparse.eval nodeValue4207 (mixedVector B) := by
    change mixedMoment B node4207 node4207Labels = _
    exact sound4207 B hB hF
  have h4248 : mixedVector B (Sum.inr 4248) = Sparse.eval nodeValue4248 (mixedVector B) := by
    change mixedMoment B node4248 node4248Labels = _
    exact sound4248 B hB hF
  have h4630 : mixedVector B (Sum.inr 4630) = Sparse.eval nodeValue4630 (mixedVector B) := by
    change mixedMoment B node4630 node4630Labels = _
    exact sound4630 B hB hF
  have h4632 : mixedVector B (Sum.inr 4632) = Sparse.eval nodeValue4632 (mixedVector B) := by
    change mixedMoment B node4632 node4632Labels = _
    exact sound4632 B hB hF
  have h4640 : mixedVector B (Sum.inr 4640) = Sparse.eval nodeValue4640 (mixedVector B) := by
    change mixedMoment B node4640 node4640Labels = _
    exact sound4640 B hB hF
  have h4759 : mixedVector B (Sum.inr 4759) = Sparse.eval nodeValue4759 (mixedVector B) := by
    change mixedMoment B node4759 node4759Labels = _
    exact sound4759 B hB hF
  have h4763 : mixedVector B (Sum.inr 4763) = Sparse.eval nodeValue4763 (mixedVector B) := by
    change mixedMoment B node4763 node4763Labels = _
    exact sound4763 B hB hF
  have h4778 : mixedVector B (Sum.inr 4778) = Sparse.eval nodeValue4778 (mixedVector B) := by
    change mixedMoment B node4778 node4778Labels = _
    exact sound4778 B hB hF
  have h4782 : mixedVector B (Sum.inr 4782) = Sparse.eval nodeValue4782 (mixedVector B) := by
    change mixedMoment B node4782 node4782Labels = _
    exact sound4782 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4887 : mixedVector B (Sum.inr 4887) = Sparse.eval nodeValue4887 (mixedVector B) := by
    change mixedMoment B node4887 node4887Labels = _
    exact sound4887 B hB hF
  have h5351 : mixedVector B (Sum.inr 5351) = Sparse.eval nodeValue5351 (mixedVector B) := by
    change mixedMoment B node5351 node5351Labels = _
    exact sound5351 B hB hF
  have h5415 : mixedVector B (Sum.inr 5415) = Sparse.eval nodeValue5415 (mixedVector B) := by
    change mixedMoment B node5415 node5415Labels = _
    exact sound5415 B hB hF
  have h5423 : mixedVector B (Sum.inr 5423) = Sparse.eval nodeValue5423 (mixedVector B) := by
    change mixedMoment B node5423 node5423Labels = _
    exact sound5423 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433 B hB hF
  simpa only [sourceForm2475, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4195, h4197, h4207, h4248, h4630, h4632, h4640, h4759, h4763, h4778, h4782, h4801, h4802, h4831, h4887, h5351, h5415, h5423, h5433, reducedSource1993] using sourceEq2475 B hB

theorem rowSound1993 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1993 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1993, numericCheck1993, reducedZero1993 B hB hF, mul_zero]

theorem reducedZero1994 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1994 (mixedVector B) = 0 := by
  have h4390 : mixedVector B (Sum.inr 4390) = Sparse.eval nodeValue4390 (mixedVector B) := by
    change mixedMoment B node4390 node4390Labels = _
    exact sound4390 B hB hF
  have h4392 : mixedVector B (Sum.inr 4392) = Sparse.eval nodeValue4392 (mixedVector B) := by
    change mixedMoment B node4392 node4392Labels = _
    exact sound4392 B hB hF
  have h4396 : mixedVector B (Sum.inr 4396) = Sparse.eval nodeValue4396 (mixedVector B) := by
    change mixedMoment B node4396 node4396Labels = _
    exact sound4396 B hB hF
  have h4435 : mixedVector B (Sum.inr 4435) = Sparse.eval nodeValue4435 (mixedVector B) := by
    change mixedMoment B node4435 node4435Labels = _
    exact sound4435 B hB hF
  have h4728 : mixedVector B (Sum.inr 4728) = Sparse.eval nodeValue4728 (mixedVector B) := by
    change mixedMoment B node4728 node4728Labels = _
    exact sound4728 B hB hF
  have h4731 : mixedVector B (Sum.inr 4731) = Sparse.eval nodeValue4731 (mixedVector B) := by
    change mixedMoment B node4731 node4731Labels = _
    exact sound4731 B hB hF
  have h4736 : mixedVector B (Sum.inr 4736) = Sparse.eval nodeValue4736 (mixedVector B) := by
    change mixedMoment B node4736 node4736Labels = _
    exact sound4736 B hB hF
  have h4797 : mixedVector B (Sum.inr 4797) = Sparse.eval nodeValue4797 (mixedVector B) := by
    change mixedMoment B node4797 node4797Labels = _
    exact sound4797 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4812 : mixedVector B (Sum.inr 4812) = Sparse.eval nodeValue4812 (mixedVector B) := by
    change mixedMoment B node4812 node4812Labels = _
    exact sound4812 B hB hF
  have h4815 : mixedVector B (Sum.inr 4815) = Sparse.eval nodeValue4815 (mixedVector B) := by
    change mixedMoment B node4815 node4815Labels = _
    exact sound4815 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4848 : mixedVector B (Sum.inr 4848) = Sparse.eval nodeValue4848 (mixedVector B) := by
    change mixedMoment B node4848 node4848Labels = _
    exact sound4848 B hB hF
  have h4851 : mixedVector B (Sum.inr 4851) = Sparse.eval nodeValue4851 (mixedVector B) := by
    change mixedMoment B node4851 node4851Labels = _
    exact sound4851 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h5072 : mixedVector B (Sum.inr 5072) = Sparse.eval nodeValue5072 (mixedVector B) := by
    change mixedMoment B node5072 node5072Labels = _
    exact sound5072 B hB hF
  have h5144 : mixedVector B (Sum.inr 5144) = Sparse.eval nodeValue5144 (mixedVector B) := by
    change mixedMoment B node5144 node5144Labels = _
    exact sound5144 B hB hF
  have h5148 : mixedVector B (Sum.inr 5148) = Sparse.eval nodeValue5148 (mixedVector B) := by
    change mixedMoment B node5148 node5148Labels = _
    exact sound5148 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168 B hB hF
  simpa only [sourceForm2476, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4390, h4392, h4396, h4435, h4728, h4731, h4736, h4797, h4798, h4802, h4812, h4815, h4832, h4834, h4848, h4851, h4865, h5072, h5144, h5148, h5168, reducedSource1994] using sourceEq2476 B hB

theorem rowSound1994 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1994 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1994, numericCheck1994, reducedZero1994 B hB hF, mul_zero]

theorem reducedZero1995 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1995 (mixedVector B) = 0 := by
  have h4345 : mixedVector B (Sum.inr 4345) = Sparse.eval nodeValue4345 (mixedVector B) := by
    change mixedMoment B node4345 node4345Labels = _
    exact sound4345 B hB hF
  have h4353 : mixedVector B (Sum.inr 4353) = Sparse.eval nodeValue4353 (mixedVector B) := by
    change mixedMoment B node4353 node4353Labels = _
    exact sound4353 B hB hF
  have h4354 : mixedVector B (Sum.inr 4354) = Sparse.eval nodeValue4354 (mixedVector B) := by
    change mixedMoment B node4354 node4354Labels = _
    exact sound4354 B hB hF
  have h4357 : mixedVector B (Sum.inr 4357) = Sparse.eval nodeValue4357 (mixedVector B) := by
    change mixedMoment B node4357 node4357Labels = _
    exact sound4357 B hB hF
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h4680 : mixedVector B (Sum.inr 4680) = Sparse.eval nodeValue4680 (mixedVector B) := by
    change mixedMoment B node4680 node4680Labels = _
    exact sound4680 B hB hF
  have h4687 : mixedVector B (Sum.inr 4687) = Sparse.eval nodeValue4687 (mixedVector B) := by
    change mixedMoment B node4687 node4687Labels = _
    exact sound4687 B hB hF
  have h4688 : mixedVector B (Sum.inr 4688) = Sparse.eval nodeValue4688 (mixedVector B) := by
    change mixedMoment B node4688 node4688Labels = _
    exact sound4688 B hB hF
  have h4690 : mixedVector B (Sum.inr 4690) = Sparse.eval nodeValue4690 (mixedVector B) := by
    change mixedMoment B node4690 node4690Labels = _
    exact sound4690 B hB hF
  have h4765 : mixedVector B (Sum.inr 4765) = Sparse.eval nodeValue4765 (mixedVector B) := by
    change mixedMoment B node4765 node4765Labels = _
    exact sound4765 B hB hF
  have h4766 : mixedVector B (Sum.inr 4766) = Sparse.eval nodeValue4766 (mixedVector B) := by
    change mixedMoment B node4766 node4766Labels = _
    exact sound4766 B hB hF
  have h4768 : mixedVector B (Sum.inr 4768) = Sparse.eval nodeValue4768 (mixedVector B) := by
    change mixedMoment B node4768 node4768Labels = _
    exact sound4768 B hB hF
  have h4803 : mixedVector B (Sum.inr 4803) = Sparse.eval nodeValue4803 (mixedVector B) := by
    change mixedMoment B node4803 node4803Labels = _
    exact sound4803 B hB hF
  have h4808 : mixedVector B (Sum.inr 4808) = Sparse.eval nodeValue4808 (mixedVector B) := by
    change mixedMoment B node4808 node4808Labels = _
    exact sound4808 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4816 : mixedVector B (Sum.inr 4816) = Sparse.eval nodeValue4816 (mixedVector B) := by
    change mixedMoment B node4816 node4816Labels = _
    exact sound4816 B hB hF
  have h4819 : mixedVector B (Sum.inr 4819) = Sparse.eval nodeValue4819 (mixedVector B) := by
    change mixedMoment B node4819 node4819Labels = _
    exact sound4819 B hB hF
  have h4821 : mixedVector B (Sum.inr 4821) = Sparse.eval nodeValue4821 (mixedVector B) := by
    change mixedMoment B node4821 node4821Labels = _
    exact sound4821 B hB hF
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h4898 : mixedVector B (Sum.inr 4898) = Sparse.eval nodeValue4898 (mixedVector B) := by
    change mixedMoment B node4898 node4898Labels = _
    exact sound4898 B hB hF
  have h5233 : mixedVector B (Sum.inr 5233) = Sparse.eval nodeValue5233 (mixedVector B) := by
    change mixedMoment B node5233 node5233Labels = _
    exact sound5233 B hB hF
  have h5244 : mixedVector B (Sum.inr 5244) = Sparse.eval nodeValue5244 (mixedVector B) := by
    change mixedMoment B node5244 node5244Labels = _
    exact sound5244 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5266 : mixedVector B (Sum.inr 5266) = Sparse.eval nodeValue5266 (mixedVector B) := by
    change mixedMoment B node5266 node5266Labels = _
    exact sound5266 B hB hF
  have h5267 : mixedVector B (Sum.inr 5267) = Sparse.eval nodeValue5267 (mixedVector B) := by
    change mixedMoment B node5267 node5267Labels = _
    exact sound5267 B hB hF
  simpa only [sourceForm2477, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4345, h4353, h4354, h4357, h4503, h4680, h4687, h4688, h4690, h4765, h4766, h4768, h4803, h4808, h4810, h4816, h4819, h4821, h4831, h4834, h4835, h4839, h4895, h4896, h4898, h5233, h5244, h5259, h5266, h5267, reducedSource1995] using sourceEq2477 B hB

theorem rowSound1995 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1995 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1995, numericCheck1995, reducedZero1995 B hB hF, mul_zero]

theorem reducedZero1996 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1996 (mixedVector B) = 0 := by
  have h1668 : mixedVector B (Sum.inr 1668) = Sparse.eval nodeValue1668 (mixedVector B) := by
    change mixedMoment B node1668 node1668Labels = _
    exact sound1668 B hB hF
  have h1681 : mixedVector B (Sum.inr 1681) = Sparse.eval nodeValue1681 (mixedVector B) := by
    change mixedMoment B node1681 node1681Labels = _
    exact sound1681 B hB hF
  have h1682 : mixedVector B (Sum.inr 1682) = Sparse.eval nodeValue1682 (mixedVector B) := by
    change mixedMoment B node1682 node1682Labels = _
    exact sound1682 B hB hF
  have h1686 : mixedVector B (Sum.inr 1686) = Sparse.eval nodeValue1686 (mixedVector B) := by
    change mixedMoment B node1686 node1686Labels = _
    exact sound1686 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h2145 : mixedVector B (Sum.inr 2145) = Sparse.eval nodeValue2145 (mixedVector B) := by
    change mixedMoment B node2145 node2145Labels = _
    exact sound2145 B hB hF
  have h2157 : mixedVector B (Sum.inr 2157) = Sparse.eval nodeValue2157 (mixedVector B) := by
    change mixedMoment B node2157 node2157Labels = _
    exact sound2157 B hB hF
  have h2158 : mixedVector B (Sum.inr 2158) = Sparse.eval nodeValue2158 (mixedVector B) := by
    change mixedMoment B node2158 node2158Labels = _
    exact sound2158 B hB hF
  have h2162 : mixedVector B (Sum.inr 2162) = Sparse.eval nodeValue2162 (mixedVector B) := by
    change mixedMoment B node2162 node2162Labels = _
    exact sound2162 B hB hF
  have h2177 : mixedVector B (Sum.inr 2177) = Sparse.eval nodeValue2177 (mixedVector B) := by
    change mixedMoment B node2177 node2177Labels = _
    exact sound2177 B hB hF
  have h2178 : mixedVector B (Sum.inr 2178) = Sparse.eval nodeValue2178 (mixedVector B) := by
    change mixedMoment B node2178 node2178Labels = _
    exact sound2178 B hB hF
  have h2179 : mixedVector B (Sum.inr 2179) = Sparse.eval nodeValue2179 (mixedVector B) := by
    change mixedMoment B node2179 node2179Labels = _
    exact sound2179 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2196 : mixedVector B (Sum.inr 2196) = Sparse.eval nodeValue2196 (mixedVector B) := by
    change mixedMoment B node2196 node2196Labels = _
    exact sound2196 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2221 : mixedVector B (Sum.inr 2221) = Sparse.eval nodeValue2221 (mixedVector B) := by
    change mixedMoment B node2221 node2221Labels = _
    exact sound2221 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h2678 : mixedVector B (Sum.inr 2678) = Sparse.eval nodeValue2678 (mixedVector B) := by
    change mixedMoment B node2678 node2678Labels = _
    exact sound2678 B hB hF
  have h2698 : mixedVector B (Sum.inr 2698) = Sparse.eval nodeValue2698 (mixedVector B) := by
    change mixedMoment B node2698 node2698Labels = _
    exact sound2698 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  simpa only [sourceForm2478, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1668, h1681, h1682, h1686, h1739, h2145, h2157, h2158, h2162, h2177, h2178, h2179, h2191, h2195, h2196, h2205, h2206, h2215, h2216, h2217, h2220, h2221, h2265, h2278, h2279, h2678, h2698, h2723, h2731, h2732, reducedSource1996] using sourceEq2478 B hB

theorem rowSound1996 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1996 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1996, numericCheck1996, reducedZero1996 B hB hF, mul_zero]

theorem reducedZero1997 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1997 (mixedVector B) = 0 := by
  have h1806 : mixedVector B (Sum.inr 1806) = Sparse.eval nodeValue1806 (mixedVector B) := by
    change mixedMoment B node1806 node1806Labels = _
    exact sound1806 B hB hF
  have h1813 : mixedVector B (Sum.inr 1813) = Sparse.eval nodeValue1813 (mixedVector B) := by
    change mixedMoment B node1813 node1813Labels = _
    exact sound1813 B hB hF
  have h1814 : mixedVector B (Sum.inr 1814) = Sparse.eval nodeValue1814 (mixedVector B) := by
    change mixedMoment B node1814 node1814Labels = _
    exact sound1814 B hB hF
  have h1816 : mixedVector B (Sum.inr 1816) = Sparse.eval nodeValue1816 (mixedVector B) := by
    change mixedMoment B node1816 node1816Labels = _
    exact sound1816 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h3395 : mixedVector B (Sum.inr 3395) = Sparse.eval nodeValue3395 (mixedVector B) := by
    change mixedMoment B node3395 node3395Labels = _
    exact sound3395 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2479, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1806, h1813, h1814, h1816, h2058, h3395, h4084, reducedSource1997] using sourceEq2479 B hB

theorem rowSound1997 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1997 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1997, numericCheck1997, reducedZero1997 B hB hF, mul_zero]

theorem reducedZero1998 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1998 (mixedVector B) = 0 := by
  have h4407 : mixedVector B (Sum.inr 4407) = Sparse.eval nodeValue4407 (mixedVector B) := by
    change mixedMoment B node4407 node4407Labels = _
    exact sound4407 B hB hF
  have h4410 : mixedVector B (Sum.inr 4410) = Sparse.eval nodeValue4410 (mixedVector B) := by
    change mixedMoment B node4410 node4410Labels = _
    exact sound4410 B hB hF
  have h4412 : mixedVector B (Sum.inr 4412) = Sparse.eval nodeValue4412 (mixedVector B) := by
    change mixedMoment B node4412 node4412Labels = _
    exact sound4412 B hB hF
  have h4424 : mixedVector B (Sum.inr 4424) = Sparse.eval nodeValue4424 (mixedVector B) := by
    change mixedMoment B node4424 node4424Labels = _
    exact sound4424 B hB hF
  have h4471 : mixedVector B (Sum.inr 4471) = Sparse.eval nodeValue4471 (mixedVector B) := by
    change mixedMoment B node4471 node4471Labels = _
    exact sound4471 B hB hF
  have h4740 : mixedVector B (Sum.inr 4740) = Sparse.eval nodeValue4740 (mixedVector B) := by
    change mixedMoment B node4740 node4740Labels = _
    exact sound4740 B hB hF
  have h4747 : mixedVector B (Sum.inr 4747) = Sparse.eval nodeValue4747 (mixedVector B) := by
    change mixedMoment B node4747 node4747Labels = _
    exact sound4747 B hB hF
  have h4750 : mixedVector B (Sum.inr 4750) = Sparse.eval nodeValue4750 (mixedVector B) := by
    change mixedMoment B node4750 node4750Labels = _
    exact sound4750 B hB hF
  have h4752 : mixedVector B (Sum.inr 4752) = Sparse.eval nodeValue4752 (mixedVector B) := by
    change mixedMoment B node4752 node4752Labels = _
    exact sound4752 B hB hF
  have h4783 : mixedVector B (Sum.inr 4783) = Sparse.eval nodeValue4783 (mixedVector B) := by
    change mixedMoment B node4783 node4783Labels = _
    exact sound4783 B hB hF
  have h4785 : mixedVector B (Sum.inr 4785) = Sparse.eval nodeValue4785 (mixedVector B) := by
    change mixedMoment B node4785 node4785Labels = _
    exact sound4785 B hB hF
  have h4787 : mixedVector B (Sum.inr 4787) = Sparse.eval nodeValue4787 (mixedVector B) := by
    change mixedMoment B node4787 node4787Labels = _
    exact sound4787 B hB hF
  have h4803 : mixedVector B (Sum.inr 4803) = Sparse.eval nodeValue4803 (mixedVector B) := by
    change mixedMoment B node4803 node4803Labels = _
    exact sound4803 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4806 : mixedVector B (Sum.inr 4806) = Sparse.eval nodeValue4806 (mixedVector B) := by
    change mixedMoment B node4806 node4806Labels = _
    exact sound4806 B hB hF
  have h4813 : mixedVector B (Sum.inr 4813) = Sparse.eval nodeValue4813 (mixedVector B) := by
    change mixedMoment B node4813 node4813Labels = _
    exact sound4813 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4836 : mixedVector B (Sum.inr 4836) = Sparse.eval nodeValue4836 (mixedVector B) := by
    change mixedMoment B node4836 node4836Labels = _
    exact sound4836 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4840 : mixedVector B (Sum.inr 4840) = Sparse.eval nodeValue4840 (mixedVector B) := by
    change mixedMoment B node4840 node4840Labels = _
    exact sound4840 B hB hF
  have h4842 : mixedVector B (Sum.inr 4842) = Sparse.eval nodeValue4842 (mixedVector B) := by
    change mixedMoment B node4842 node4842Labels = _
    exact sound4842 B hB hF
  have h4867 : mixedVector B (Sum.inr 4867) = Sparse.eval nodeValue4867 (mixedVector B) := by
    change mixedMoment B node4867 node4867Labels = _
    exact sound4867 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h4870 : mixedVector B (Sum.inr 4870) = Sparse.eval nodeValue4870 (mixedVector B) := by
    change mixedMoment B node4870 node4870Labels = _
    exact sound4870 B hB hF
  have h5105 : mixedVector B (Sum.inr 5105) = Sparse.eval nodeValue5105 (mixedVector B) := by
    change mixedMoment B node5105 node5105Labels = _
    exact sound5105 B hB hF
  have h5138 : mixedVector B (Sum.inr 5138) = Sparse.eval nodeValue5138 (mixedVector B) := by
    change mixedMoment B node5138 node5138Labels = _
    exact sound5138 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172 B hB hF
  have h5173 : mixedVector B (Sum.inr 5173) = Sparse.eval nodeValue5173 (mixedVector B) := by
    change mixedMoment B node5173 node5173Labels = _
    exact sound5173 B hB hF
  simpa only [sourceForm2481, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4407, h4410, h4412, h4424, h4471, h4740, h4747, h4750, h4752, h4783, h4785, h4787, h4803, h4805, h4806, h4813, h4835, h4836, h4838, h4839, h4840, h4842, h4867, h4869, h4870, h5105, h5138, h5170, h5172, h5173, reducedSource1998] using sourceEq2481 B hB

theorem rowSound1998 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1998 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1998, numericCheck1998, reducedZero1998 B hB hF, mul_zero]

theorem reducedZero1999 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1999 (mixedVector B) = 0 := by
  have h4342 : mixedVector B (Sum.inr 4342) = Sparse.eval nodeValue4342 (mixedVector B) := by
    change mixedMoment B node4342 node4342Labels = _
    exact sound4342 B hB hF
  have h4347 : mixedVector B (Sum.inr 4347) = Sparse.eval nodeValue4347 (mixedVector B) := by
    change mixedMoment B node4347 node4347Labels = _
    exact sound4347 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
  have h4357 : mixedVector B (Sum.inr 4357) = Sparse.eval nodeValue4357 (mixedVector B) := by
    change mixedMoment B node4357 node4357Labels = _
    exact sound4357 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  have h4677 : mixedVector B (Sum.inr 4677) = Sparse.eval nodeValue4677 (mixedVector B) := by
    change mixedMoment B node4677 node4677Labels = _
    exact sound4677 B hB hF
  have h4682 : mixedVector B (Sum.inr 4682) = Sparse.eval nodeValue4682 (mixedVector B) := by
    change mixedMoment B node4682 node4682Labels = _
    exact sound4682 B hB hF
  have h4684 : mixedVector B (Sum.inr 4684) = Sparse.eval nodeValue4684 (mixedVector B) := by
    change mixedMoment B node4684 node4684Labels = _
    exact sound4684 B hB hF
  have h4690 : mixedVector B (Sum.inr 4690) = Sparse.eval nodeValue4690 (mixedVector B) := by
    change mixedMoment B node4690 node4690Labels = _
    exact sound4690 B hB hF
  have h4761 : mixedVector B (Sum.inr 4761) = Sparse.eval nodeValue4761 (mixedVector B) := by
    change mixedMoment B node4761 node4761Labels = _
    exact sound4761 B hB hF
  have h4763 : mixedVector B (Sum.inr 4763) = Sparse.eval nodeValue4763 (mixedVector B) := by
    change mixedMoment B node4763 node4763Labels = _
    exact sound4763 B hB hF
  have h4768 : mixedVector B (Sum.inr 4768) = Sparse.eval nodeValue4768 (mixedVector B) := by
    change mixedMoment B node4768 node4768Labels = _
    exact sound4768 B hB hF
  have h4815 : mixedVector B (Sum.inr 4815) = Sparse.eval nodeValue4815 (mixedVector B) := by
    change mixedMoment B node4815 node4815Labels = _
    exact sound4815 B hB hF
  have h4817 : mixedVector B (Sum.inr 4817) = Sparse.eval nodeValue4817 (mixedVector B) := by
    change mixedMoment B node4817 node4817Labels = _
    exact sound4817 B hB hF
  have h4821 : mixedVector B (Sum.inr 4821) = Sparse.eval nodeValue4821 (mixedVector B) := by
    change mixedMoment B node4821 node4821Labels = _
    exact sound4821 B hB hF
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h4901 : mixedVector B (Sum.inr 4901) = Sparse.eval nodeValue4901 (mixedVector B) := by
    change mixedMoment B node4901 node4901Labels = _
    exact sound4901 B hB hF
  have h5229 : mixedVector B (Sum.inr 5229) = Sparse.eval nodeValue5229 (mixedVector B) := by
    change mixedMoment B node5229 node5229Labels = _
    exact sound5229 B hB hF
  have h5242 : mixedVector B (Sum.inr 5242) = Sparse.eval nodeValue5242 (mixedVector B) := by
    change mixedMoment B node5242 node5242Labels = _
    exact sound5242 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  simpa only [sourceForm2482, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4342, h4347, h4349, h4357, h4499, h4677, h4682, h4684, h4690, h4761, h4763, h4768, h4815, h4817, h4821, h4831, h4834, h4835, h4839, h4843, h4846, h4895, h4896, h4901, h5229, h5242, h5259, h5260, h5275, reducedSource1999] using sourceEq2482 B hB

theorem rowSound1999 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1999 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1999, numericCheck1999, reducedZero1999 B hB hF, mul_zero]

theorem sourceRowsAt1984 : MixedData.sourceRows (1984 : Fin 2425) =
    MixedData.row1984 := by decide +kernel

theorem sourceRowsAt1985 : MixedData.sourceRows (1985 : Fin 2425) =
    MixedData.row1985 := by decide +kernel

theorem sourceRowsAt1986 : MixedData.sourceRows (1986 : Fin 2425) =
    MixedData.row1986 := by decide +kernel

theorem sourceRowsAt1987 : MixedData.sourceRows (1987 : Fin 2425) =
    MixedData.row1987 := by decide +kernel

theorem sourceRowsAt1988 : MixedData.sourceRows (1988 : Fin 2425) =
    MixedData.row1988 := by decide +kernel

theorem sourceRowsAt1989 : MixedData.sourceRows (1989 : Fin 2425) =
    MixedData.row1989 := by decide +kernel

theorem sourceRowsAt1990 : MixedData.sourceRows (1990 : Fin 2425) =
    MixedData.row1990 := by decide +kernel

theorem sourceRowsAt1991 : MixedData.sourceRows (1991 : Fin 2425) =
    MixedData.row1991 := by decide +kernel

theorem sourceRowsAt1992 : MixedData.sourceRows (1992 : Fin 2425) =
    MixedData.row1992 := by decide +kernel

theorem sourceRowsAt1993 : MixedData.sourceRows (1993 : Fin 2425) =
    MixedData.row1993 := by decide +kernel

theorem sourceRowsAt1994 : MixedData.sourceRows (1994 : Fin 2425) =
    MixedData.row1994 := by decide +kernel

theorem sourceRowsAt1995 : MixedData.sourceRows (1995 : Fin 2425) =
    MixedData.row1995 := by decide +kernel

theorem sourceRowsAt1996 : MixedData.sourceRows (1996 : Fin 2425) =
    MixedData.row1996 := by decide +kernel

theorem sourceRowsAt1997 : MixedData.sourceRows (1997 : Fin 2425) =
    MixedData.row1997 := by decide +kernel

theorem sourceRowsAt1998 : MixedData.sourceRows (1998 : Fin 2425) =
    MixedData.row1998 := by decide +kernel

theorem sourceRowsAt1999 : MixedData.sourceRows (1999 : Fin 2425) =
    MixedData.row1999 := by decide +kernel

theorem chunkSound124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 124) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1984 ∨ k.val = 1985 ∨ k.val = 1986 ∨ k.val = 1987 ∨ k.val = 1988 ∨ k.val = 1989 ∨ k.val = 1990 ∨ k.val = 1991 ∨ k.val = 1992 ∨ k.val = 1993 ∨ k.val = 1994 ∨ k.val = 1995 ∨ k.val = 1996 ∨ k.val = 1997 ∨ k.val = 1998 ∨ k.val = 1999 := by omega
  rcases heq with h1984 | h1985 | h1986 | h1987 | h1988 | h1989 | h1990 | h1991 | h1992 | h1993 | h1994 | h1995 | h1996 | h1997 | h1998 | h1999
  · have he : k = (1984 : Fin 2425) := Fin.ext h1984
    subst k
    rw [sourceRowsAt1984]
    exact rowSound1984 B hB hF
  · have he : k = (1985 : Fin 2425) := Fin.ext h1985
    subst k
    rw [sourceRowsAt1985]
    exact rowSound1985 B hB hF
  · have he : k = (1986 : Fin 2425) := Fin.ext h1986
    subst k
    rw [sourceRowsAt1986]
    exact rowSound1986 B hB hF
  · have he : k = (1987 : Fin 2425) := Fin.ext h1987
    subst k
    rw [sourceRowsAt1987]
    exact rowSound1987 B hB hF
  · have he : k = (1988 : Fin 2425) := Fin.ext h1988
    subst k
    rw [sourceRowsAt1988]
    exact rowSound1988 B hB hF
  · have he : k = (1989 : Fin 2425) := Fin.ext h1989
    subst k
    rw [sourceRowsAt1989]
    exact rowSound1989 B hB hF
  · have he : k = (1990 : Fin 2425) := Fin.ext h1990
    subst k
    rw [sourceRowsAt1990]
    exact rowSound1990 B hB hF
  · have he : k = (1991 : Fin 2425) := Fin.ext h1991
    subst k
    rw [sourceRowsAt1991]
    exact rowSound1991 B hB hF
  · have he : k = (1992 : Fin 2425) := Fin.ext h1992
    subst k
    rw [sourceRowsAt1992]
    exact rowSound1992 B hB hF
  · have he : k = (1993 : Fin 2425) := Fin.ext h1993
    subst k
    rw [sourceRowsAt1993]
    exact rowSound1993 B hB hF
  · have he : k = (1994 : Fin 2425) := Fin.ext h1994
    subst k
    rw [sourceRowsAt1994]
    exact rowSound1994 B hB hF
  · have he : k = (1995 : Fin 2425) := Fin.ext h1995
    subst k
    rw [sourceRowsAt1995]
    exact rowSound1995 B hB hF
  · have he : k = (1996 : Fin 2425) := Fin.ext h1996
    subst k
    rw [sourceRowsAt1996]
    exact rowSound1996 B hB hF
  · have he : k = (1997 : Fin 2425) := Fin.ext h1997
    subst k
    rw [sourceRowsAt1997]
    exact rowSound1997 B hB hF
  · have he : k = (1998 : Fin 2425) := Fin.ext h1998
    subst k
    rw [sourceRowsAt1998]
    exact rowSound1998 B hB hF
  · have he : k = (1999 : Fin 2425) := Fin.ext h1999
    subst k
    rw [sourceRowsAt1999]
    exact rowSound1999 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
