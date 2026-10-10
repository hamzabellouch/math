import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources11

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero288 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource288 (mixedVector B) = 0 := by
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3907 : mixedVector B (Sum.inr 3907) = Sparse.eval nodeValue3907 (mixedVector B) := by
    change mixedMoment B node3907 node3907Labels = _
    exact sound3907 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm343, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3038, h3840, h3845, h3854, h3857, h3907, h4092, reducedSource288] using sourceEq343 B hB

theorem rowSound288 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row288 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck288, numericCheck288, reducedZero288 B hB hF, mul_zero]

theorem reducedZero289 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource289 (mixedVector B) = 0 := by
  have h1357 : mixedVector B (Sum.inr 1357) = Sparse.eval nodeValue1357 (mixedVector B) := by
    change mixedMoment B node1357 node1357Labels = _
    exact sound1357 B hB hF
  have h1359 : mixedVector B (Sum.inr 1359) = Sparse.eval nodeValue1359 (mixedVector B) := by
    change mixedMoment B node1359 node1359Labels = _
    exact sound1359 B hB hF
  have h1362 : mixedVector B (Sum.inr 1362) = Sparse.eval nodeValue1362 (mixedVector B) := by
    change mixedMoment B node1362 node1362Labels = _
    exact sound1362 B hB hF
  have h1367 : mixedVector B (Sum.inr 1367) = Sparse.eval nodeValue1367 (mixedVector B) := by
    change mixedMoment B node1367 node1367Labels = _
    exact sound1367 B hB hF
  have h1422 : mixedVector B (Sum.inr 1422) = Sparse.eval nodeValue1422 (mixedVector B) := by
    change mixedMoment B node1422 node1422Labels = _
    exact sound1422 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm344, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1357, h1359, h1362, h1367, h1422, h3038, h4092, reducedSource289] using sourceEq344 B hB

theorem rowSound289 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row289 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck289, numericCheck289, reducedZero289 B hB hF, mul_zero]

theorem reducedZero290 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource290 (mixedVector B) = 0 := by
  have h1367 : mixedVector B (Sum.inr 1367) = Sparse.eval nodeValue1367 (mixedVector B) := by
    change mixedMoment B node1367 node1367Labels = _
    exact sound1367 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h2974 : mixedVector B (Sum.inr 2974) = Sparse.eval nodeValue2974 (mixedVector B) := by
    change mixedMoment B node2974 node2974Labels = _
    exact sound2974 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm345, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1367, h2881, h2974, h3038, h3051, h3054, h4092, reducedSource290] using sourceEq345 B hB

theorem rowSound290 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row290 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck290, numericCheck290, reducedZero290 B hB hF, mul_zero]

theorem reducedZero291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource291 (mixedVector B) = 0 := by
  have h2579 : mixedVector B (Sum.inr 2579) = Sparse.eval nodeValue2579 (mixedVector B) := by
    change mixedMoment B node2579 node2579Labels = _
    exact sound2579 B hB hF
  have h2582 : mixedVector B (Sum.inr 2582) = Sparse.eval nodeValue2582 (mixedVector B) := by
    change mixedMoment B node2582 node2582Labels = _
    exact sound2582 B hB hF
  have h3007 : mixedVector B (Sum.inr 3007) = Sparse.eval nodeValue3007 (mixedVector B) := by
    change mixedMoment B node3007 node3007Labels = _
    exact sound3007 B hB hF
  have h3010 : mixedVector B (Sum.inr 3010) = Sparse.eval nodeValue3010 (mixedVector B) := by
    change mixedMoment B node3010 node3010Labels = _
    exact sound3010 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm346, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2579, h2582, h3007, h3010, h3038, h3854, h4092, reducedSource291] using sourceEq346 B hB

theorem rowSound291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row291 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck291, numericCheck291, reducedZero291 B hB hF, mul_zero]

theorem reducedZero292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource292 (mixedVector B) = 0 := by
  have h1357 : mixedVector B (Sum.inr 1357) = Sparse.eval nodeValue1357 (mixedVector B) := by
    change mixedMoment B node1357 node1357Labels = _
    exact sound1357 B hB hF
  have h2861 : mixedVector B (Sum.inr 2861) = Sparse.eval nodeValue2861 (mixedVector B) := by
    change mixedMoment B node2861 node2861Labels = _
    exact sound2861 B hB hF
  have h3007 : mixedVector B (Sum.inr 3007) = Sparse.eval nodeValue3007 (mixedVector B) := by
    change mixedMoment B node3007 node3007Labels = _
    exact sound3007 B hB hF
  have h3036 : mixedVector B (Sum.inr 3036) = Sparse.eval nodeValue3036 (mixedVector B) := by
    change mixedMoment B node3036 node3036Labels = _
    exact sound3036 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm347, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1357, h2861, h3007, h3036, h3038, h4092, reducedSource292] using sourceEq347 B hB

theorem rowSound292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row292 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck292, numericCheck292, reducedZero292 B hB hF, mul_zero]

theorem reducedZero293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource293 (mixedVector B) = 0 := by
  have h2547 : mixedVector B (Sum.inr 2547) = Sparse.eval nodeValue2547 (mixedVector B) := by
    change mixedMoment B node2547 node2547Labels = _
    exact sound2547 B hB hF
  have h2580 : mixedVector B (Sum.inr 2580) = Sparse.eval nodeValue2580 (mixedVector B) := by
    change mixedMoment B node2580 node2580Labels = _
    exact sound2580 B hB hF
  have h2971 : mixedVector B (Sum.inr 2971) = Sparse.eval nodeValue2971 (mixedVector B) := by
    change mixedMoment B node2971 node2971Labels = _
    exact sound2971 B hB hF
  have h2974 : mixedVector B (Sum.inr 2974) = Sparse.eval nodeValue2974 (mixedVector B) := by
    change mixedMoment B node2974 node2974Labels = _
    exact sound2974 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm348, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2547, h2580, h2971, h2974, h3038, h3840, h4092, reducedSource293] using sourceEq348 B hB

theorem rowSound293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row293 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck293, numericCheck293, reducedZero293 B hB hF, mul_zero]

theorem reducedZero294 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource294 (mixedVector B) = 0 := by
  have h2558 : mixedVector B (Sum.inr 2558) = Sparse.eval nodeValue2558 (mixedVector B) := by
    change mixedMoment B node2558 node2558Labels = _
    exact sound2558 B hB hF
  have h2861 : mixedVector B (Sum.inr 2861) = Sparse.eval nodeValue2861 (mixedVector B) := by
    change mixedMoment B node2861 node2861Labels = _
    exact sound2861 B hB hF
  have h2867 : mixedVector B (Sum.inr 2867) = Sparse.eval nodeValue2867 (mixedVector B) := by
    change mixedMoment B node2867 node2867Labels = _
    exact sound2867 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm349, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2558, h2861, h2867, h2881, h3038, h3845, h4092, reducedSource294] using sourceEq349 B hB

theorem rowSound294 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row294 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck294, numericCheck294, reducedZero294 B hB hF, mul_zero]

theorem reducedZero295 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource295 (mixedVector B) = 0 := by
  have h1362 : mixedVector B (Sum.inr 1362) = Sparse.eval nodeValue1362 (mixedVector B) := by
    change mixedMoment B node1362 node1362Labels = _
    exact sound1362 B hB hF
  have h2867 : mixedVector B (Sum.inr 2867) = Sparse.eval nodeValue2867 (mixedVector B) := by
    change mixedMoment B node2867 node2867Labels = _
    exact sound2867 B hB hF
  have h2971 : mixedVector B (Sum.inr 2971) = Sparse.eval nodeValue2971 (mixedVector B) := by
    change mixedMoment B node2971 node2971Labels = _
    exact sound2971 B hB hF
  have h3010 : mixedVector B (Sum.inr 3010) = Sparse.eval nodeValue3010 (mixedVector B) := by
    change mixedMoment B node3010 node3010Labels = _
    exact sound3010 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3040 : mixedVector B (Sum.inr 3040) = Sparse.eval nodeValue3040 (mixedVector B) := by
    change mixedMoment B node3040 node3040Labels = _
    exact sound3040 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm350, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1362, h2867, h2971, h3010, h3038, h3040, h4092, reducedSource295] using sourceEq350 B hB

theorem rowSound295 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row295 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck295, numericCheck295, reducedZero295 B hB hF, mul_zero]

theorem reducedZero296 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource296 (mixedVector B) = 0 := by
  have h2036 : mixedVector B (Sum.inr 2036) = Sparse.eval nodeValue2036 (mixedVector B) := by
    change mixedMoment B node2036 node2036Labels = _
    exact sound2036 B hB hF
  have h2037 : mixedVector B (Sum.inr 2037) = Sparse.eval nodeValue2037 (mixedVector B) := by
    change mixedMoment B node2037 node2037Labels = _
    exact sound2037 B hB hF
  have h2038 : mixedVector B (Sum.inr 2038) = Sparse.eval nodeValue2038 (mixedVector B) := by
    change mixedMoment B node2038 node2038Labels = _
    exact sound2038 B hB hF
  have h2059 : mixedVector B (Sum.inr 2059) = Sparse.eval nodeValue2059 (mixedVector B) := by
    change mixedMoment B node2059 node2059Labels = _
    exact sound2059 B hB hF
  have h2254 : mixedVector B (Sum.inr 2254) = Sparse.eval nodeValue2254 (mixedVector B) := by
    change mixedMoment B node2254 node2254Labels = _
    exact sound2254 B hB hF
  have h2661 : mixedVector B (Sum.inr 2661) = Sparse.eval nodeValue2661 (mixedVector B) := by
    change mixedMoment B node2661 node2661Labels = _
    exact sound2661 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h2677 : mixedVector B (Sum.inr 2677) = Sparse.eval nodeValue2677 (mixedVector B) := by
    change mixedMoment B node2677 node2677Labels = _
    exact sound2677 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h3015 : mixedVector B (Sum.inr 3015) = Sparse.eval nodeValue3015 (mixedVector B) := by
    change mixedMoment B node3015 node3015Labels = _
    exact sound3015 B hB hF
  have h3016 : mixedVector B (Sum.inr 3016) = Sparse.eval nodeValue3016 (mixedVector B) := by
    change mixedMoment B node3016 node3016Labels = _
    exact sound3016 B hB hF
  have h3018 : mixedVector B (Sum.inr 3018) = Sparse.eval nodeValue3018 (mixedVector B) := by
    change mixedMoment B node3018 node3018Labels = _
    exact sound3018 B hB hF
  have h3028 : mixedVector B (Sum.inr 3028) = Sparse.eval nodeValue3028 (mixedVector B) := by
    change mixedMoment B node3028 node3028Labels = _
    exact sound3028 B hB hF
  have h3029 : mixedVector B (Sum.inr 3029) = Sparse.eval nodeValue3029 (mixedVector B) := by
    change mixedMoment B node3029 node3029Labels = _
    exact sound3029 B hB hF
  have h3035 : mixedVector B (Sum.inr 3035) = Sparse.eval nodeValue3035 (mixedVector B) := by
    change mixedMoment B node3035 node3035Labels = _
    exact sound3035 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3042 : mixedVector B (Sum.inr 3042) = Sparse.eval nodeValue3042 (mixedVector B) := by
    change mixedMoment B node3042 node3042Labels = _
    exact sound3042 B hB hF
  have h3044 : mixedVector B (Sum.inr 3044) = Sparse.eval nodeValue3044 (mixedVector B) := by
    change mixedMoment B node3044 node3044Labels = _
    exact sound3044 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3088 : mixedVector B (Sum.inr 3088) = Sparse.eval nodeValue3088 (mixedVector B) := by
    change mixedMoment B node3088 node3088Labels = _
    exact sound3088 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3196 : mixedVector B (Sum.inr 3196) = Sparse.eval nodeValue3196 (mixedVector B) := by
    change mixedMoment B node3196 node3196Labels = _
    exact sound3196 B hB hF
  have h3198 : mixedVector B (Sum.inr 3198) = Sparse.eval nodeValue3198 (mixedVector B) := by
    change mixedMoment B node3198 node3198Labels = _
    exact sound3198 B hB hF
  have h3210 : mixedVector B (Sum.inr 3210) = Sparse.eval nodeValue3210 (mixedVector B) := by
    change mixedMoment B node3210 node3210Labels = _
    exact sound3210 B hB hF
  have h3224 : mixedVector B (Sum.inr 3224) = Sparse.eval nodeValue3224 (mixedVector B) := by
    change mixedMoment B node3224 node3224Labels = _
    exact sound3224 B hB hF
  simpa only [sourceForm353, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2036, h2037, h2038, h2059, h2254, h2661, h2670, h2672, h2677, h2722, h3015, h3016, h3018, h3028, h3029, h3035, h3038, h3039, h3042, h3044, h3052, h3054, h3064, h3086, h3088, h3101, h3196, h3198, h3210, h3224, reducedSource296] using sourceEq353 B hB

theorem rowSound296 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row296 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck296, numericCheck296, reducedZero296 B hB hF, mul_zero]

theorem reducedZero297 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource297 (mixedVector B) = 0 := by
  have h2560 : mixedVector B (Sum.inr 2560) = Sparse.eval nodeValue2560 (mixedVector B) := by
    change mixedMoment B node2560 node2560Labels = _
    exact sound2560 B hB hF
  have h3375 : mixedVector B (Sum.inr 3375) = Sparse.eval nodeValue3375 (mixedVector B) := by
    change mixedMoment B node3375 node3375Labels = _
    exact sound3375 B hB hF
  have h3379 : mixedVector B (Sum.inr 3379) = Sparse.eval nodeValue3379 (mixedVector B) := by
    change mixedMoment B node3379 node3379Labels = _
    exact sound3379 B hB hF
  have h3391 : mixedVector B (Sum.inr 3391) = Sparse.eval nodeValue3391 (mixedVector B) := by
    change mixedMoment B node3391 node3391Labels = _
    exact sound3391 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm354, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2560, h3375, h3379, h3391, h3533, h3541, h4084, reducedSource297] using sourceEq354 B hB

theorem rowSound297 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row297 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck297, numericCheck297, reducedZero297 B hB hF, mul_zero]

theorem reducedZero298 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource298 (mixedVector B) = 0 := by
  have h2034 : mixedVector B (Sum.inr 2034) = Sparse.eval nodeValue2034 (mixedVector B) := by
    change mixedMoment B node2034 node2034Labels = _
    exact sound2034 B hB hF
  have h2037 : mixedVector B (Sum.inr 2037) = Sparse.eval nodeValue2037 (mixedVector B) := by
    change mixedMoment B node2037 node2037Labels = _
    exact sound2037 B hB hF
  have h2039 : mixedVector B (Sum.inr 2039) = Sparse.eval nodeValue2039 (mixedVector B) := by
    change mixedMoment B node2039 node2039Labels = _
    exact sound2039 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm355, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2034, h2037, h2039, h2058, h2279, h3541, h4084, reducedSource298] using sourceEq355 B hB

theorem rowSound298 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row298 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck298, numericCheck298, reducedZero298 B hB hF, mul_zero]

theorem reducedZero299 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource299 (mixedVector B) = 0 := by
  have h3151 : mixedVector B (Sum.inr 3151) = Sparse.eval nodeValue3151 (mixedVector B) := by
    change mixedMoment B node3151 node3151Labels = _
    exact sound3151 B hB hF
  have h3379 : mixedVector B (Sum.inr 3379) = Sparse.eval nodeValue3379 (mixedVector B) := by
    change mixedMoment B node3379 node3379Labels = _
    exact sound3379 B hB hF
  have h3382 : mixedVector B (Sum.inr 3382) = Sparse.eval nodeValue3382 (mixedVector B) := by
    change mixedMoment B node3382 node3382Labels = _
    exact sound3382 B hB hF
  have h3383 : mixedVector B (Sum.inr 3383) = Sparse.eval nodeValue3383 (mixedVector B) := by
    change mixedMoment B node3383 node3383Labels = _
    exact sound3383 B hB hF
  have h3395 : mixedVector B (Sum.inr 3395) = Sparse.eval nodeValue3395 (mixedVector B) := by
    change mixedMoment B node3395 node3395Labels = _
    exact sound3395 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm356, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3151, h3379, h3382, h3383, h3395, h3541, h4084, reducedSource299] using sourceEq356 B hB

theorem rowSound299 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row299 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck299, numericCheck299, reducedZero299 B hB hF, mul_zero]

theorem reducedZero300 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource300 (mixedVector B) = 0 := by
  have h2034 : mixedVector B (Sum.inr 2034) = Sparse.eval nodeValue2034 (mixedVector B) := by
    change mixedMoment B node2034 node2034Labels = _
    exact sound2034 B hB hF
  have h2555 : mixedVector B (Sum.inr 2555) = Sparse.eval nodeValue2555 (mixedVector B) := by
    change mixedMoment B node2555 node2555Labels = _
    exact sound2555 B hB hF
  have h3382 : mixedVector B (Sum.inr 3382) = Sparse.eval nodeValue3382 (mixedVector B) := by
    change mixedMoment B node3382 node3382Labels = _
    exact sound3382 B hB hF
  have h3528 : mixedVector B (Sum.inr 3528) = Sparse.eval nodeValue3528 (mixedVector B) := by
    change mixedMoment B node3528 node3528Labels = _
    exact sound3528 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm357, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2034, h2555, h3382, h3528, h3539, h3541, h4084, reducedSource300] using sourceEq357 B hB

theorem rowSound300 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row300 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck300, numericCheck300, reducedZero300 B hB hF, mul_zero]

theorem reducedZero301 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource301 (mixedVector B) = 0 := by
  have h3279 : mixedVector B (Sum.inr 3279) = Sparse.eval nodeValue3279 (mixedVector B) := by
    change mixedMoment B node3279 node3279Labels = _
    exact sound3279 B hB hF
  have h3280 : mixedVector B (Sum.inr 3280) = Sparse.eval nodeValue3280 (mixedVector B) := by
    change mixedMoment B node3280 node3280Labels = _
    exact sound3280 B hB hF
  have h3282 : mixedVector B (Sum.inr 3282) = Sparse.eval nodeValue3282 (mixedVector B) := by
    change mixedMoment B node3282 node3282Labels = _
    exact sound3282 B hB hF
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h3434 : mixedVector B (Sum.inr 3434) = Sparse.eval nodeValue3434 (mixedVector B) := by
    change mixedMoment B node3434 node3434Labels = _
    exact sound3434 B hB hF
  have h3466 : mixedVector B (Sum.inr 3466) = Sparse.eval nodeValue3466 (mixedVector B) := by
    change mixedMoment B node3466 node3466Labels = _
    exact sound3466 B hB hF
  have h3467 : mixedVector B (Sum.inr 3467) = Sparse.eval nodeValue3467 (mixedVector B) := by
    change mixedMoment B node3467 node3467Labels = _
    exact sound3467 B hB hF
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3529 : mixedVector B (Sum.inr 3529) = Sparse.eval nodeValue3529 (mixedVector B) := by
    change mixedMoment B node3529 node3529Labels = _
    exact sound3529 B hB hF
  have h3532 : mixedVector B (Sum.inr 3532) = Sparse.eval nodeValue3532 (mixedVector B) := by
    change mixedMoment B node3532 node3532Labels = _
    exact sound3532 B hB hF
  have h3536 : mixedVector B (Sum.inr 3536) = Sparse.eval nodeValue3536 (mixedVector B) := by
    change mixedMoment B node3536 node3536Labels = _
    exact sound3536 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3543 : mixedVector B (Sum.inr 3543) = Sparse.eval nodeValue3543 (mixedVector B) := by
    change mixedMoment B node3543 node3543Labels = _
    exact sound3543 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3568 : mixedVector B (Sum.inr 3568) = Sparse.eval nodeValue3568 (mixedVector B) := by
    change mixedMoment B node3568 node3568Labels = _
    exact sound3568 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3851 : mixedVector B (Sum.inr 3851) = Sparse.eval nodeValue3851 (mixedVector B) := by
    change mixedMoment B node3851 node3851Labels = _
    exact sound3851 B hB hF
  have h3858 : mixedVector B (Sum.inr 3858) = Sparse.eval nodeValue3858 (mixedVector B) := by
    change mixedMoment B node3858 node3858Labels = _
    exact sound3858 B hB hF
  simpa only [sourceForm361, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3279, h3280, h3282, h3290, h3434, h3466, h3467, h3476, h3529, h3532, h3536, h3539, h3543, h3544, h3568, h3571, h3580, h3805, h3848, h3851, h3858, reducedSource301] using sourceEq361 B hB

theorem rowSound301 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row301 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck301, numericCheck301, reducedZero301 B hB hF, mul_zero]

theorem reducedZero302 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource302 (mixedVector B) = 0 := by
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3901 : mixedVector B (Sum.inr 3901) = Sparse.eval nodeValue3901 (mixedVector B) := by
    change mixedMoment B node3901 node3901Labels = _
    exact sound3901 B hB hF
  have h3902 : mixedVector B (Sum.inr 3902) = Sparse.eval nodeValue3902 (mixedVector B) := by
    change mixedMoment B node3902 node3902Labels = _
    exact sound3902 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm362, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2709, h3800, h3871, h3901, h3902, h4091, reducedSource302] using sourceEq362 B hB

theorem rowSound302 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row302 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck302, numericCheck302, reducedZero302 B hB hF, mul_zero]

theorem reducedZero303 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource303 (mixedVector B) = 0 := by
  have h1206 : mixedVector B (Sum.inr 1206) = Sparse.eval nodeValue1206 (mixedVector B) := by
    change mixedMoment B node1206 node1206Labels = _
    exact sound1206 B hB hF
  have h1208 : mixedVector B (Sum.inr 1208) = Sparse.eval nodeValue1208 (mixedVector B) := by
    change mixedMoment B node1208 node1208Labels = _
    exact sound1208 B hB hF
  have h1213 : mixedVector B (Sum.inr 1213) = Sparse.eval nodeValue1213 (mixedVector B) := by
    change mixedMoment B node1213 node1213Labels = _
    exact sound1213 B hB hF
  have h1247 : mixedVector B (Sum.inr 1247) = Sparse.eval nodeValue1247 (mixedVector B) := by
    change mixedMoment B node1247 node1247Labels = _
    exact sound1247 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm363, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1206, h1208, h1213, h1247, h2709, h4091, reducedSource303] using sourceEq363 B hB

theorem rowSound303 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row303 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck303, numericCheck303, reducedZero303 B hB hF, mul_zero]

theorem sourceRowsAt288 : MixedData.sourceRows (288 : Fin 2425) =
    MixedData.row288 := by decide +kernel

theorem sourceRowsAt289 : MixedData.sourceRows (289 : Fin 2425) =
    MixedData.row289 := by decide +kernel

theorem sourceRowsAt290 : MixedData.sourceRows (290 : Fin 2425) =
    MixedData.row290 := by decide +kernel

theorem sourceRowsAt291 : MixedData.sourceRows (291 : Fin 2425) =
    MixedData.row291 := by decide +kernel

theorem sourceRowsAt292 : MixedData.sourceRows (292 : Fin 2425) =
    MixedData.row292 := by decide +kernel

theorem sourceRowsAt293 : MixedData.sourceRows (293 : Fin 2425) =
    MixedData.row293 := by decide +kernel

theorem sourceRowsAt294 : MixedData.sourceRows (294 : Fin 2425) =
    MixedData.row294 := by decide +kernel

theorem sourceRowsAt295 : MixedData.sourceRows (295 : Fin 2425) =
    MixedData.row295 := by decide +kernel

theorem sourceRowsAt296 : MixedData.sourceRows (296 : Fin 2425) =
    MixedData.row296 := by decide +kernel

theorem sourceRowsAt297 : MixedData.sourceRows (297 : Fin 2425) =
    MixedData.row297 := by decide +kernel

theorem sourceRowsAt298 : MixedData.sourceRows (298 : Fin 2425) =
    MixedData.row298 := by decide +kernel

theorem sourceRowsAt299 : MixedData.sourceRows (299 : Fin 2425) =
    MixedData.row299 := by decide +kernel

theorem sourceRowsAt300 : MixedData.sourceRows (300 : Fin 2425) =
    MixedData.row300 := by decide +kernel

theorem sourceRowsAt301 : MixedData.sourceRows (301 : Fin 2425) =
    MixedData.row301 := by decide +kernel

theorem sourceRowsAt302 : MixedData.sourceRows (302 : Fin 2425) =
    MixedData.row302 := by decide +kernel

theorem sourceRowsAt303 : MixedData.sourceRows (303 : Fin 2425) =
    MixedData.row303 := by decide +kernel

theorem chunkSound18 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 18) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 288 ∨ k.val = 289 ∨ k.val = 290 ∨ k.val = 291 ∨ k.val = 292 ∨ k.val = 293 ∨ k.val = 294 ∨ k.val = 295 ∨ k.val = 296 ∨ k.val = 297 ∨ k.val = 298 ∨ k.val = 299 ∨ k.val = 300 ∨ k.val = 301 ∨ k.val = 302 ∨ k.val = 303 := by omega
  rcases heq with h288 | h289 | h290 | h291 | h292 | h293 | h294 | h295 | h296 | h297 | h298 | h299 | h300 | h301 | h302 | h303
  · have he : k = (288 : Fin 2425) := Fin.ext h288
    subst k
    rw [sourceRowsAt288]
    exact rowSound288 B hB hF
  · have he : k = (289 : Fin 2425) := Fin.ext h289
    subst k
    rw [sourceRowsAt289]
    exact rowSound289 B hB hF
  · have he : k = (290 : Fin 2425) := Fin.ext h290
    subst k
    rw [sourceRowsAt290]
    exact rowSound290 B hB hF
  · have he : k = (291 : Fin 2425) := Fin.ext h291
    subst k
    rw [sourceRowsAt291]
    exact rowSound291 B hB hF
  · have he : k = (292 : Fin 2425) := Fin.ext h292
    subst k
    rw [sourceRowsAt292]
    exact rowSound292 B hB hF
  · have he : k = (293 : Fin 2425) := Fin.ext h293
    subst k
    rw [sourceRowsAt293]
    exact rowSound293 B hB hF
  · have he : k = (294 : Fin 2425) := Fin.ext h294
    subst k
    rw [sourceRowsAt294]
    exact rowSound294 B hB hF
  · have he : k = (295 : Fin 2425) := Fin.ext h295
    subst k
    rw [sourceRowsAt295]
    exact rowSound295 B hB hF
  · have he : k = (296 : Fin 2425) := Fin.ext h296
    subst k
    rw [sourceRowsAt296]
    exact rowSound296 B hB hF
  · have he : k = (297 : Fin 2425) := Fin.ext h297
    subst k
    rw [sourceRowsAt297]
    exact rowSound297 B hB hF
  · have he : k = (298 : Fin 2425) := Fin.ext h298
    subst k
    rw [sourceRowsAt298]
    exact rowSound298 B hB hF
  · have he : k = (299 : Fin 2425) := Fin.ext h299
    subst k
    rw [sourceRowsAt299]
    exact rowSound299 B hB hF
  · have he : k = (300 : Fin 2425) := Fin.ext h300
    subst k
    rw [sourceRowsAt300]
    exact rowSound300 B hB hF
  · have he : k = (301 : Fin 2425) := Fin.ext h301
    subst k
    rw [sourceRowsAt301]
    exact rowSound301 B hB hF
  · have he : k = (302 : Fin 2425) := Fin.ext h302
    subst k
    rw [sourceRowsAt302]
    exact rowSound302 B hB hF
  · have he : k = (303 : Fin 2425) := Fin.ext h303
    subst k
    rw [sourceRowsAt303]
    exact rowSound303 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
