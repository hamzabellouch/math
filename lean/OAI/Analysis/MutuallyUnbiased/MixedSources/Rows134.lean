import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic134
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources85

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2144 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2144 (mixedVector B) = 0 := by
  have h1690 : mixedVector B (Sum.inr 1690) = Sparse.eval nodeValue1690 (mixedVector B) := by
    change mixedMoment B node1690 node1690Labels = _
    exact sound1690 B hB hF
  have h2184 : mixedVector B (Sum.inr 2184) = Sparse.eval nodeValue2184 (mixedVector B) := by
    change mixedMoment B node2184 node2184Labels = _
    exact sound2184 B hB hF
  have h3255 : mixedVector B (Sum.inr 3255) = Sparse.eval nodeValue3255 (mixedVector B) := by
    change mixedMoment B node3255 node3255Labels = _
    exact sound3255 B hB hF
  have h3264 : mixedVector B (Sum.inr 3264) = Sparse.eval nodeValue3264 (mixedVector B) := by
    change mixedMoment B node3264 node3264Labels = _
    exact sound3264 B hB hF
  have h3273 : mixedVector B (Sum.inr 3273) = Sparse.eval nodeValue3273 (mixedVector B) := by
    change mixedMoment B node3273 node3273Labels = _
    exact sound3273 B hB hF
  have h4064 : mixedVector B (Sum.inr 4064) = Sparse.eval nodeValue4064 (mixedVector B) := by
    change mixedMoment B node4064 node4064Labels = _
    exact sound4064 B hB hF
  simpa only [sourceForm2720, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1690, h2184, h3255, h3264, h3273, h4064, reducedSource2144] using sourceEq2720 B hB

theorem rowSound2144 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2144 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2144, numericCheck2144, reducedZero2144 B hB hF, mul_zero]

theorem reducedZero2145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2145 (mixedVector B) = 0 := by
  have h1681 : mixedVector B (Sum.inr 1681) = Sparse.eval nodeValue1681 (mixedVector B) := by
    change mixedMoment B node1681 node1681Labels = _
    exact sound1681 B hB hF
  have h2657 : mixedVector B (Sum.inr 2657) = Sparse.eval nodeValue2657 (mixedVector B) := by
    change mixedMoment B node2657 node2657Labels = _
    exact sound2657 B hB hF
  have h3258 : mixedVector B (Sum.inr 3258) = Sparse.eval nodeValue3258 (mixedVector B) := by
    change mixedMoment B node3258 node3258Labels = _
    exact sound3258 B hB hF
  have h3265 : mixedVector B (Sum.inr 3265) = Sparse.eval nodeValue3265 (mixedVector B) := by
    change mixedMoment B node3265 node3265Labels = _
    exact sound3265 B hB hF
  have h3270 : mixedVector B (Sum.inr 3270) = Sparse.eval nodeValue3270 (mixedVector B) := by
    change mixedMoment B node3270 node3270Labels = _
    exact sound3270 B hB hF
  have h4065 : mixedVector B (Sum.inr 4065) = Sparse.eval nodeValue4065 (mixedVector B) := by
    change mixedMoment B node4065 node4065Labels = _
    exact sound4065 B hB hF
  simpa only [sourceForm2725, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1681, h2657, h3258, h3265, h3270, h4065, reducedSource2145] using sourceEq2725 B hB

theorem rowSound2145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2145 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2145, numericCheck2145, reducedZero2145 B hB hF, mul_zero]

theorem reducedZero2146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2146 (mixedVector B) = 0 := by
  have h1691 : mixedVector B (Sum.inr 1691) = Sparse.eval nodeValue1691 (mixedVector B) := by
    change mixedMoment B node1691 node1691Labels = _
    exact sound1691 B hB hF
  have h3261 : mixedVector B (Sum.inr 3261) = Sparse.eval nodeValue3261 (mixedVector B) := by
    change mixedMoment B node3261 node3261Labels = _
    exact sound3261 B hB hF
  have h3265 : mixedVector B (Sum.inr 3265) = Sparse.eval nodeValue3265 (mixedVector B) := by
    change mixedMoment B node3265 node3265Labels = _
    exact sound3265 B hB hF
  have h3274 : mixedVector B (Sum.inr 3274) = Sparse.eval nodeValue3274 (mixedVector B) := by
    change mixedMoment B node3274 node3274Labels = _
    exact sound3274 B hB hF
  have h4065 : mixedVector B (Sum.inr 4065) = Sparse.eval nodeValue4065 (mixedVector B) := by
    change mixedMoment B node4065 node4065Labels = _
    exact sound4065 B hB hF
  simpa only [sourceForm2726, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1691, h3261, h3265, h3274, h4065, reducedSource2146] using sourceEq2726 B hB

theorem rowSound2146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2146 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2146, numericCheck2146, reducedZero2146 B hB hF, mul_zero]

theorem reducedZero2147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2147 (mixedVector B) = 0 := by
  have h2161 : mixedVector B (Sum.inr 2161) = Sparse.eval nodeValue2161 (mixedVector B) := by
    change mixedMoment B node2161 node2161Labels = _
    exact sound2161 B hB hF
  have h2163 : mixedVector B (Sum.inr 2163) = Sparse.eval nodeValue2163 (mixedVector B) := by
    change mixedMoment B node2163 node2163Labels = _
    exact sound2163 B hB hF
  have h2169 : mixedVector B (Sum.inr 2169) = Sparse.eval nodeValue2169 (mixedVector B) := by
    change mixedMoment B node2169 node2169Labels = _
    exact sound2169 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  simpa only [sourceForm2728, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2161, h2163, h2169, h4076, reducedSource2147] using sourceEq2728 B hB

theorem rowSound2147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2147 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2147, numericCheck2147, reducedZero2147 B hB hF, mul_zero]

theorem reducedZero2148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2148 (mixedVector B) = 0 := by
  have h2155 : mixedVector B (Sum.inr 2155) = Sparse.eval nodeValue2155 (mixedVector B) := by
    change mixedMoment B node2155 node2155Labels = _
    exact sound2155 B hB hF
  have h2159 : mixedVector B (Sum.inr 2159) = Sparse.eval nodeValue2159 (mixedVector B) := by
    change mixedMoment B node2159 node2159Labels = _
    exact sound2159 B hB hF
  have h2168 : mixedVector B (Sum.inr 2168) = Sparse.eval nodeValue2168 (mixedVector B) := by
    change mixedMoment B node2168 node2168Labels = _
    exact sound2168 B hB hF
  have h2273 : mixedVector B (Sum.inr 2273) = Sparse.eval nodeValue2273 (mixedVector B) := by
    change mixedMoment B node2273 node2273Labels = _
    exact sound2273 B hB hF
  have h3596 : mixedVector B (Sum.inr 3596) = Sparse.eval nodeValue3596 (mixedVector B) := by
    change mixedMoment B node3596 node3596Labels = _
    exact sound3596 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  simpa only [sourceForm2729, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2155, h2159, h2168, h2273, h3596, h4076, reducedSource2148] using sourceEq2729 B hB

theorem rowSound2148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2148 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2148, numericCheck2148, reducedZero2148 B hB hF, mul_zero]

theorem reducedZero2149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2149 (mixedVector B) = 0 := by
  have h2164 : mixedVector B (Sum.inr 2164) = Sparse.eval nodeValue2164 (mixedVector B) := by
    change mixedMoment B node2164 node2164Labels = _
    exact sound2164 B hB hF
  have h2168 : mixedVector B (Sum.inr 2168) = Sparse.eval nodeValue2168 (mixedVector B) := by
    change mixedMoment B node2168 node2168Labels = _
    exact sound2168 B hB hF
  have h2169 : mixedVector B (Sum.inr 2169) = Sparse.eval nodeValue2169 (mixedVector B) := by
    change mixedMoment B node2169 node2169Labels = _
    exact sound2169 B hB hF
  have h2286 : mixedVector B (Sum.inr 2286) = Sparse.eval nodeValue2286 (mixedVector B) := by
    change mixedMoment B node2286 node2286Labels = _
    exact sound2286 B hB hF
  have h3423 : mixedVector B (Sum.inr 3423) = Sparse.eval nodeValue3423 (mixedVector B) := by
    change mixedMoment B node3423 node3423Labels = _
    exact sound3423 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  simpa only [sourceForm2730, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2164, h2168, h2169, h2286, h3423, h4076, reducedSource2149] using sourceEq2730 B hB

theorem rowSound2149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2149 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2149, numericCheck2149, reducedZero2149 B hB hF, mul_zero]

theorem reducedZero2150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2150 (mixedVector B) = 0 := by
  have h2168 : mixedVector B (Sum.inr 2168) = Sparse.eval nodeValue2168 (mixedVector B) := by
    change mixedMoment B node2168 node2168Labels = _
    exact sound2168 B hB hF
  have h3415 : mixedVector B (Sum.inr 3415) = Sparse.eval nodeValue3415 (mixedVector B) := by
    change mixedMoment B node3415 node3415Labels = _
    exact sound3415 B hB hF
  have h3422 : mixedVector B (Sum.inr 3422) = Sparse.eval nodeValue3422 (mixedVector B) := by
    change mixedMoment B node3422 node3422Labels = _
    exact sound3422 B hB hF
  have h3423 : mixedVector B (Sum.inr 3423) = Sparse.eval nodeValue3423 (mixedVector B) := by
    change mixedMoment B node3423 node3423Labels = _
    exact sound3423 B hB hF
  have h3596 : mixedVector B (Sum.inr 3596) = Sparse.eval nodeValue3596 (mixedVector B) := by
    change mixedMoment B node3596 node3596Labels = _
    exact sound3596 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  simpa only [sourceForm2731, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2168, h3415, h3422, h3423, h3596, h4076, reducedSource2150] using sourceEq2731 B hB

theorem rowSound2150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2150 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2150, numericCheck2150, reducedZero2150 B hB hF, mul_zero]

theorem reducedZero2151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2151 (mixedVector B) = 0 := by
  have h3419 : mixedVector B (Sum.inr 3419) = Sparse.eval nodeValue3419 (mixedVector B) := by
    change mixedMoment B node3419 node3419Labels = _
    exact sound3419 B hB hF
  have h3422 : mixedVector B (Sum.inr 3422) = Sparse.eval nodeValue3422 (mixedVector B) := by
    change mixedMoment B node3422 node3422Labels = _
    exact sound3422 B hB hF
  have h3423 : mixedVector B (Sum.inr 3423) = Sparse.eval nodeValue3423 (mixedVector B) := by
    change mixedMoment B node3423 node3423Labels = _
    exact sound3423 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  simpa only [sourceForm2732, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3419, h3422, h3423, h4076, reducedSource2151] using sourceEq2732 B hB

theorem rowSound2151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2151 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2151, numericCheck2151, reducedZero2151 B hB hF, mul_zero]

theorem reducedZero2152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2152 (mixedVector B) = 0 := by
  have h2169 : mixedVector B (Sum.inr 2169) = Sparse.eval nodeValue2169 (mixedVector B) := by
    change mixedMoment B node2169 node2169Labels = _
    exact sound2169 B hB hF
  have h3423 : mixedVector B (Sum.inr 3423) = Sparse.eval nodeValue3423 (mixedVector B) := by
    change mixedMoment B node3423 node3423Labels = _
    exact sound3423 B hB hF
  have h3512 : mixedVector B (Sum.inr 3512) = Sparse.eval nodeValue3512 (mixedVector B) := by
    change mixedMoment B node3512 node3512Labels = _
    exact sound3512 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  simpa only [sourceForm2733, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2169, h3423, h3512, h4076, reducedSource2152] using sourceEq2733 B hB

theorem rowSound2152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2152 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2152, numericCheck2152, reducedZero2152 B hB hF, mul_zero]

theorem reducedZero2153 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2153 (mixedVector B) = 0 := by
  have h2147 : mixedVector B (Sum.inr 2147) = Sparse.eval nodeValue2147 (mixedVector B) := by
    change mixedMoment B node2147 node2147Labels = _
    exact sound2147 B hB hF
  have h2151 : mixedVector B (Sum.inr 2151) = Sparse.eval nodeValue2151 (mixedVector B) := by
    change mixedMoment B node2151 node2151Labels = _
    exact sound2151 B hB hF
  have h2153 : mixedVector B (Sum.inr 2153) = Sparse.eval nodeValue2153 (mixedVector B) := by
    change mixedMoment B node2153 node2153Labels = _
    exact sound2153 B hB hF
  have h2165 : mixedVector B (Sum.inr 2165) = Sparse.eval nodeValue2165 (mixedVector B) := by
    change mixedMoment B node2165 node2165Labels = _
    exact sound2165 B hB hF
  have h2256 : mixedVector B (Sum.inr 2256) = Sparse.eval nodeValue2256 (mixedVector B) := by
    change mixedMoment B node2256 node2256Labels = _
    exact sound2256 B hB hF
  have h3457 : mixedVector B (Sum.inr 3457) = Sparse.eval nodeValue3457 (mixedVector B) := by
    change mixedMoment B node3457 node3457Labels = _
    exact sound3457 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2740, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2147, h2151, h2153, h2165, h2256, h3457, h4074, reducedSource2153] using sourceEq2740 B hB

theorem rowSound2153 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2153 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2153, numericCheck2153, reducedZero2153 B hB hF, mul_zero]

theorem reducedZero2154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2154 (mixedVector B) = 0 := by
  have h2160 : mixedVector B (Sum.inr 2160) = Sparse.eval nodeValue2160 (mixedVector B) := by
    change mixedMoment B node2160 node2160Labels = _
    exact sound2160 B hB hF
  have h2162 : mixedVector B (Sum.inr 2162) = Sparse.eval nodeValue2162 (mixedVector B) := by
    change mixedMoment B node2162 node2162Labels = _
    exact sound2162 B hB hF
  have h2165 : mixedVector B (Sum.inr 2165) = Sparse.eval nodeValue2165 (mixedVector B) := by
    change mixedMoment B node2165 node2165Labels = _
    exact sound2165 B hB hF
  have h2180 : mixedVector B (Sum.inr 2180) = Sparse.eval nodeValue2180 (mixedVector B) := by
    change mixedMoment B node2180 node2180Labels = _
    exact sound2180 B hB hF
  have h2186 : mixedVector B (Sum.inr 2186) = Sparse.eval nodeValue2186 (mixedVector B) := by
    change mixedMoment B node2186 node2186Labels = _
    exact sound2186 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2741, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2160, h2162, h2165, h2180, h2186, h4074, reducedSource2154] using sourceEq2741 B hB

theorem rowSound2154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2154 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2154, numericCheck2154, reducedZero2154 B hB hF, mul_zero]

theorem reducedZero2155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2155 (mixedVector B) = 0 := by
  have h2140 : mixedVector B (Sum.inr 2140) = Sparse.eval nodeValue2140 (mixedVector B) := by
    change mixedMoment B node2140 node2140Labels = _
    exact sound2140 B hB hF
  have h2143 : mixedVector B (Sum.inr 2143) = Sparse.eval nodeValue2143 (mixedVector B) := by
    change mixedMoment B node2143 node2143Labels = _
    exact sound2143 B hB hF
  have h2151 : mixedVector B (Sum.inr 2151) = Sparse.eval nodeValue2151 (mixedVector B) := by
    change mixedMoment B node2151 node2151Labels = _
    exact sound2151 B hB hF
  have h2239 : mixedVector B (Sum.inr 2239) = Sparse.eval nodeValue2239 (mixedVector B) := by
    change mixedMoment B node2239 node2239Labels = _
    exact sound2239 B hB hF
  have h3588 : mixedVector B (Sum.inr 3588) = Sparse.eval nodeValue3588 (mixedVector B) := by
    change mixedMoment B node3588 node3588Labels = _
    exact sound3588 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2742, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2140, h2143, h2151, h2239, h3588, h4074, reducedSource2155] using sourceEq2742 B hB

theorem rowSound2155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2155 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2155, numericCheck2155, reducedZero2155 B hB hF, mul_zero]

theorem reducedZero2156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2156 (mixedVector B) = 0 := by
  have h3408 : mixedVector B (Sum.inr 3408) = Sparse.eval nodeValue3408 (mixedVector B) := by
    change mixedMoment B node3408 node3408Labels = _
    exact sound3408 B hB hF
  have h3411 : mixedVector B (Sum.inr 3411) = Sparse.eval nodeValue3411 (mixedVector B) := by
    change mixedMoment B node3411 node3411Labels = _
    exact sound3411 B hB hF
  have h3413 : mixedVector B (Sum.inr 3413) = Sparse.eval nodeValue3413 (mixedVector B) := by
    change mixedMoment B node3413 node3413Labels = _
    exact sound3413 B hB hF
  have h3420 : mixedVector B (Sum.inr 3420) = Sparse.eval nodeValue3420 (mixedVector B) := by
    change mixedMoment B node3420 node3420Labels = _
    exact sound3420 B hB hF
  have h3457 : mixedVector B (Sum.inr 3457) = Sparse.eval nodeValue3457 (mixedVector B) := by
    change mixedMoment B node3457 node3457Labels = _
    exact sound3457 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2743, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3408, h3411, h3413, h3420, h3457, h4074, reducedSource2156] using sourceEq2743 B hB

theorem rowSound2156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2156 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2156, numericCheck2156, reducedZero2156 B hB hF, mul_zero]

theorem reducedZero2157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2157 (mixedVector B) = 0 := by
  have h2181 : mixedVector B (Sum.inr 2181) = Sparse.eval nodeValue2181 (mixedVector B) := by
    change mixedMoment B node2181 node2181Labels = _
    exact sound2181 B hB hF
  have h2185 : mixedVector B (Sum.inr 2185) = Sparse.eval nodeValue2185 (mixedVector B) := by
    change mixedMoment B node2185 node2185Labels = _
    exact sound2185 B hB hF
  have h2186 : mixedVector B (Sum.inr 2186) = Sparse.eval nodeValue2186 (mixedVector B) := by
    change mixedMoment B node2186 node2186Labels = _
    exact sound2186 B hB hF
  have h2223 : mixedVector B (Sum.inr 2223) = Sparse.eval nodeValue2223 (mixedVector B) := by
    change mixedMoment B node2223 node2223Labels = _
    exact sound2223 B hB hF
  have h3420 : mixedVector B (Sum.inr 3420) = Sparse.eval nodeValue3420 (mixedVector B) := by
    change mixedMoment B node3420 node3420Labels = _
    exact sound3420 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2744, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2181, h2185, h2186, h2223, h3420, h4074, reducedSource2157] using sourceEq2744 B hB

theorem rowSound2157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2157 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2157, numericCheck2157, reducedZero2157 B hB hF, mul_zero]

theorem reducedZero2158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2158 (mixedVector B) = 0 := by
  have h2185 : mixedVector B (Sum.inr 2185) = Sparse.eval nodeValue2185 (mixedVector B) := by
    change mixedMoment B node2185 node2185Labels = _
    exact sound2185 B hB hF
  have h3403 : mixedVector B (Sum.inr 3403) = Sparse.eval nodeValue3403 (mixedVector B) := by
    change mixedMoment B node3403 node3403Labels = _
    exact sound3403 B hB hF
  have h3411 : mixedVector B (Sum.inr 3411) = Sparse.eval nodeValue3411 (mixedVector B) := by
    change mixedMoment B node3411 node3411Labels = _
    exact sound3411 B hB hF
  have h3420 : mixedVector B (Sum.inr 3420) = Sparse.eval nodeValue3420 (mixedVector B) := by
    change mixedMoment B node3420 node3420Labels = _
    exact sound3420 B hB hF
  have h3588 : mixedVector B (Sum.inr 3588) = Sparse.eval nodeValue3588 (mixedVector B) := by
    change mixedMoment B node3588 node3588Labels = _
    exact sound3588 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2745, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2185, h3403, h3411, h3420, h3588, h4074, reducedSource2158] using sourceEq2745 B hB

theorem rowSound2158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2158 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2158, numericCheck2158, reducedZero2158 B hB hF, mul_zero]

theorem reducedZero2159 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2159 (mixedVector B) = 0 := by
  have h2143 : mixedVector B (Sum.inr 2143) = Sparse.eval nodeValue2143 (mixedVector B) := by
    change mixedMoment B node2143 node2143Labels = _
    exact sound2143 B hB hF
  have h2176 : mixedVector B (Sum.inr 2176) = Sparse.eval nodeValue2176 (mixedVector B) := by
    change mixedMoment B node2176 node2176Labels = _
    exact sound2176 B hB hF
  have h2185 : mixedVector B (Sum.inr 2185) = Sparse.eval nodeValue2185 (mixedVector B) := by
    change mixedMoment B node2185 node2185Labels = _
    exact sound2185 B hB hF
  have h2212 : mixedVector B (Sum.inr 2212) = Sparse.eval nodeValue2212 (mixedVector B) := by
    change mixedMoment B node2212 node2212Labels = _
    exact sound2212 B hB hF
  have h3588 : mixedVector B (Sum.inr 3588) = Sparse.eval nodeValue3588 (mixedVector B) := by
    change mixedMoment B node3588 node3588Labels = _
    exact sound3588 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2747, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2143, h2176, h2185, h2212, h3588, h4074, reducedSource2159] using sourceEq2747 B hB

theorem rowSound2159 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2159 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2159, numericCheck2159, reducedZero2159 B hB hF, mul_zero]

theorem sourceRowsAt2144 : MixedData.sourceRows (2144 : Fin 2425) =
    MixedData.row2144 := by decide +kernel

theorem sourceRowsAt2145 : MixedData.sourceRows (2145 : Fin 2425) =
    MixedData.row2145 := by decide +kernel

theorem sourceRowsAt2146 : MixedData.sourceRows (2146 : Fin 2425) =
    MixedData.row2146 := by decide +kernel

theorem sourceRowsAt2147 : MixedData.sourceRows (2147 : Fin 2425) =
    MixedData.row2147 := by decide +kernel

theorem sourceRowsAt2148 : MixedData.sourceRows (2148 : Fin 2425) =
    MixedData.row2148 := by decide +kernel

theorem sourceRowsAt2149 : MixedData.sourceRows (2149 : Fin 2425) =
    MixedData.row2149 := by decide +kernel

theorem sourceRowsAt2150 : MixedData.sourceRows (2150 : Fin 2425) =
    MixedData.row2150 := by decide +kernel

theorem sourceRowsAt2151 : MixedData.sourceRows (2151 : Fin 2425) =
    MixedData.row2151 := by decide +kernel

theorem sourceRowsAt2152 : MixedData.sourceRows (2152 : Fin 2425) =
    MixedData.row2152 := by decide +kernel

theorem sourceRowsAt2153 : MixedData.sourceRows (2153 : Fin 2425) =
    MixedData.row2153 := by decide +kernel

theorem sourceRowsAt2154 : MixedData.sourceRows (2154 : Fin 2425) =
    MixedData.row2154 := by decide +kernel

theorem sourceRowsAt2155 : MixedData.sourceRows (2155 : Fin 2425) =
    MixedData.row2155 := by decide +kernel

theorem sourceRowsAt2156 : MixedData.sourceRows (2156 : Fin 2425) =
    MixedData.row2156 := by decide +kernel

theorem sourceRowsAt2157 : MixedData.sourceRows (2157 : Fin 2425) =
    MixedData.row2157 := by decide +kernel

theorem sourceRowsAt2158 : MixedData.sourceRows (2158 : Fin 2425) =
    MixedData.row2158 := by decide +kernel

theorem sourceRowsAt2159 : MixedData.sourceRows (2159 : Fin 2425) =
    MixedData.row2159 := by decide +kernel

theorem chunkSound134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 134) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2144 ∨ k.val = 2145 ∨ k.val = 2146 ∨ k.val = 2147 ∨ k.val = 2148 ∨ k.val = 2149 ∨ k.val = 2150 ∨ k.val = 2151 ∨ k.val = 2152 ∨ k.val = 2153 ∨ k.val = 2154 ∨ k.val = 2155 ∨ k.val = 2156 ∨ k.val = 2157 ∨ k.val = 2158 ∨ k.val = 2159 := by omega
  rcases heq with h2144 | h2145 | h2146 | h2147 | h2148 | h2149 | h2150 | h2151 | h2152 | h2153 | h2154 | h2155 | h2156 | h2157 | h2158 | h2159
  · have he : k = (2144 : Fin 2425) := Fin.ext h2144
    subst k
    rw [sourceRowsAt2144]
    exact rowSound2144 B hB hF
  · have he : k = (2145 : Fin 2425) := Fin.ext h2145
    subst k
    rw [sourceRowsAt2145]
    exact rowSound2145 B hB hF
  · have he : k = (2146 : Fin 2425) := Fin.ext h2146
    subst k
    rw [sourceRowsAt2146]
    exact rowSound2146 B hB hF
  · have he : k = (2147 : Fin 2425) := Fin.ext h2147
    subst k
    rw [sourceRowsAt2147]
    exact rowSound2147 B hB hF
  · have he : k = (2148 : Fin 2425) := Fin.ext h2148
    subst k
    rw [sourceRowsAt2148]
    exact rowSound2148 B hB hF
  · have he : k = (2149 : Fin 2425) := Fin.ext h2149
    subst k
    rw [sourceRowsAt2149]
    exact rowSound2149 B hB hF
  · have he : k = (2150 : Fin 2425) := Fin.ext h2150
    subst k
    rw [sourceRowsAt2150]
    exact rowSound2150 B hB hF
  · have he : k = (2151 : Fin 2425) := Fin.ext h2151
    subst k
    rw [sourceRowsAt2151]
    exact rowSound2151 B hB hF
  · have he : k = (2152 : Fin 2425) := Fin.ext h2152
    subst k
    rw [sourceRowsAt2152]
    exact rowSound2152 B hB hF
  · have he : k = (2153 : Fin 2425) := Fin.ext h2153
    subst k
    rw [sourceRowsAt2153]
    exact rowSound2153 B hB hF
  · have he : k = (2154 : Fin 2425) := Fin.ext h2154
    subst k
    rw [sourceRowsAt2154]
    exact rowSound2154 B hB hF
  · have he : k = (2155 : Fin 2425) := Fin.ext h2155
    subst k
    rw [sourceRowsAt2155]
    exact rowSound2155 B hB hF
  · have he : k = (2156 : Fin 2425) := Fin.ext h2156
    subst k
    rw [sourceRowsAt2156]
    exact rowSound2156 B hB hF
  · have he : k = (2157 : Fin 2425) := Fin.ext h2157
    subst k
    rw [sourceRowsAt2157]
    exact rowSound2157 B hB hF
  · have he : k = (2158 : Fin 2425) := Fin.ext h2158
    subst k
    rw [sourceRowsAt2158]
    exact rowSound2158 B hB hF
  · have he : k = (2159 : Fin 2425) := Fin.ext h2159
    subst k
    rw [sourceRowsAt2159]
    exact rowSound2159 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
