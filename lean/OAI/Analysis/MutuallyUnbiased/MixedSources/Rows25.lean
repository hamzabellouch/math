import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources15

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero400 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource400 (mixedVector B) = 0 := by
  have h2639 : mixedVector B (Sum.inr 2639) = Sparse.eval nodeValue2639 (mixedVector B) := by
    change mixedMoment B node2639 node2639Labels = _
    exact sound2639 B hB hF
  have h2871 : mixedVector B (Sum.inr 2871) = Sparse.eval nodeValue2871 (mixedVector B) := by
    change mixedMoment B node2871 node2871Labels = _
    exact sound2871 B hB hF
  have h2975 : mixedVector B (Sum.inr 2975) = Sparse.eval nodeValue2975 (mixedVector B) := by
    change mixedMoment B node2975 node2975Labels = _
    exact sound2975 B hB hF
  have h2979 : mixedVector B (Sum.inr 2979) = Sparse.eval nodeValue2979 (mixedVector B) := by
    change mixedMoment B node2979 node2979Labels = _
    exact sound2979 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm478, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2639, h2871, h2975, h2979, h3055, h3884, h4092, reducedSource400] using sourceEq478 B hB

theorem rowSound400 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row400 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck400, numericCheck400, reducedZero400 B hB hF, mul_zero]

theorem reducedZero401 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource401 (mixedVector B) = 0 := by
  have h2882 : mixedVector B (Sum.inr 2882) = Sparse.eval nodeValue2882 (mixedVector B) := by
    change mixedMoment B node2882 node2882Labels = _
    exact sound2882 B hB hF
  have h2886 : mixedVector B (Sum.inr 2886) = Sparse.eval nodeValue2886 (mixedVector B) := by
    change mixedMoment B node2886 node2886Labels = _
    exact sound2886 B hB hF
  have h2889 : mixedVector B (Sum.inr 2889) = Sparse.eval nodeValue2889 (mixedVector B) := by
    change mixedMoment B node2889 node2889Labels = _
    exact sound2889 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3963 : mixedVector B (Sum.inr 3963) = Sparse.eval nodeValue3963 (mixedVector B) := by
    change mixedMoment B node3963 node3963Labels = _
    exact sound3963 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm479, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2882, h2886, h2889, h3055, h3963, h4092, reducedSource401] using sourceEq479 B hB

theorem rowSound401 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row401 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck401, numericCheck401, reducedZero401 B hB hF, mul_zero]

theorem reducedZero402 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource402 (mixedVector B) = 0 := by
  have h1375 : mixedVector B (Sum.inr 1375) = Sparse.eval nodeValue1375 (mixedVector B) := by
    change mixedMoment B node1375 node1375Labels = _
    exact sound1375 B hB hF
  have h2889 : mixedVector B (Sum.inr 2889) = Sparse.eval nodeValue2889 (mixedVector B) := by
    change mixedMoment B node2889 node2889Labels = _
    exact sound2889 B hB hF
  have h2979 : mixedVector B (Sum.inr 2979) = Sparse.eval nodeValue2979 (mixedVector B) := by
    change mixedMoment B node2979 node2979Labels = _
    exact sound2979 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm480, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1375, h2889, h2979, h3054, h3055, h4092, reducedSource402] using sourceEq480 B hB

theorem rowSound402 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row402 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck402, numericCheck402, reducedZero402 B hB hF, mul_zero]

theorem reducedZero403 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource403 (mixedVector B) = 0 := by
  have h2643 : mixedVector B (Sum.inr 2643) = Sparse.eval nodeValue2643 (mixedVector B) := by
    change mixedMoment B node2643 node2643Labels = _
    exact sound2643 B hB hF
  have h3044 : mixedVector B (Sum.inr 3044) = Sparse.eval nodeValue3044 (mixedVector B) := by
    change mixedMoment B node3044 node3044Labels = _
    exact sound3044 B hB hF
  have h3046 : mixedVector B (Sum.inr 3046) = Sparse.eval nodeValue3046 (mixedVector B) := by
    change mixedMoment B node3046 node3046Labels = _
    exact sound3046 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3886 : mixedVector B (Sum.inr 3886) = Sparse.eval nodeValue3886 (mixedVector B) := by
    change mixedMoment B node3886 node3886Labels = _
    exact sound3886 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm481, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2643, h3044, h3046, h3055, h3886, h4092, reducedSource403] using sourceEq481 B hB

theorem rowSound403 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row403 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck403, numericCheck403, reducedZero403 B hB hF, mul_zero]

theorem reducedZero404 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource404 (mixedVector B) = 0 := by
  have h2129 : mixedVector B (Sum.inr 2129) = Sparse.eval nodeValue2129 (mixedVector B) := by
    change mixedMoment B node2129 node2129Labels = _
    exact sound2129 B hB hF
  have h2130 : mixedVector B (Sum.inr 2130) = Sparse.eval nodeValue2130 (mixedVector B) := by
    change mixedMoment B node2130 node2130Labels = _
    exact sound2130 B hB hF
  have h2138 : mixedVector B (Sum.inr 2138) = Sparse.eval nodeValue2138 (mixedVector B) := by
    change mixedMoment B node2138 node2138Labels = _
    exact sound2138 B hB hF
  have h2251 : mixedVector B (Sum.inr 2251) = Sparse.eval nodeValue2251 (mixedVector B) := by
    change mixedMoment B node2251 node2251Labels = _
    exact sound2251 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2282 : mixedVector B (Sum.inr 2282) = Sparse.eval nodeValue2282 (mixedVector B) := by
    change mixedMoment B node2282 node2282Labels = _
    exact sound2282 B hB hF
  have h2629 : mixedVector B (Sum.inr 2629) = Sparse.eval nodeValue2629 (mixedVector B) := by
    change mixedMoment B node2629 node2629Labels = _
    exact sound2629 B hB hF
  have h2643 : mixedVector B (Sum.inr 2643) = Sparse.eval nodeValue2643 (mixedVector B) := by
    change mixedMoment B node2643 node2643Labels = _
    exact sound2643 B hB hF
  have h2713 : mixedVector B (Sum.inr 2713) = Sparse.eval nodeValue2713 (mixedVector B) := by
    change mixedMoment B node2713 node2713Labels = _
    exact sound2713 B hB hF
  have h2729 : mixedVector B (Sum.inr 2729) = Sparse.eval nodeValue2729 (mixedVector B) := by
    change mixedMoment B node2729 node2729Labels = _
    exact sound2729 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h2758 : mixedVector B (Sum.inr 2758) = Sparse.eval nodeValue2758 (mixedVector B) := by
    change mixedMoment B node2758 node2758Labels = _
    exact sound2758 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  have h2771 : mixedVector B (Sum.inr 2771) = Sparse.eval nodeValue2771 (mixedVector B) := by
    change mixedMoment B node2771 node2771Labels = _
    exact sound2771 B hB hF
  have h2776 : mixedVector B (Sum.inr 2776) = Sparse.eval nodeValue2776 (mixedVector B) := by
    change mixedMoment B node2776 node2776Labels = _
    exact sound2776 B hB hF
  have h3092 : mixedVector B (Sum.inr 3092) = Sparse.eval nodeValue3092 (mixedVector B) := by
    change mixedMoment B node3092 node3092Labels = _
    exact sound3092 B hB hF
  have h3110 : mixedVector B (Sum.inr 3110) = Sparse.eval nodeValue3110 (mixedVector B) := by
    change mixedMoment B node3110 node3110Labels = _
    exact sound3110 B hB hF
  have h3117 : mixedVector B (Sum.inr 3117) = Sparse.eval nodeValue3117 (mixedVector B) := by
    change mixedMoment B node3117 node3117Labels = _
    exact sound3117 B hB hF
  simpa only [sourceForm483, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2129, h2130, h2138, h2251, h2276, h2278, h2282, h2629, h2643, h2713, h2729, h2731, h2751, h2758, h2765, h2767, h2771, h2776, h3092, h3110, h3117, reducedSource404] using sourceEq483 B hB

theorem rowSound404 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row404 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck404, numericCheck404, reducedZero404 B hB hF, mul_zero]

theorem reducedZero405 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource405 (mixedVector B) = 0 := by
  have h2888 : mixedVector B (Sum.inr 2888) = Sparse.eval nodeValue2888 (mixedVector B) := by
    change mixedMoment B node2888 node2888Labels = _
    exact sound2888 B hB hF
  have h3392 : mixedVector B (Sum.inr 3392) = Sparse.eval nodeValue3392 (mixedVector B) := by
    change mixedMoment B node3392 node3392Labels = _
    exact sound3392 B hB hF
  have h3397 : mixedVector B (Sum.inr 3397) = Sparse.eval nodeValue3397 (mixedVector B) := by
    change mixedMoment B node3397 node3397Labels = _
    exact sound3397 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm485, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2888, h3392, h3397, h3548, h3584, h4084, reducedSource405] using sourceEq485 B hB

theorem rowSound405 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row405 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck405, numericCheck405, reducedZero405 B hB hF, mul_zero]

theorem reducedZero406 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource406 (mixedVector B) = 0 := by
  have h2108 : mixedVector B (Sum.inr 2108) = Sparse.eval nodeValue2108 (mixedVector B) := by
    change mixedMoment B node2108 node2108Labels = _
    exact sound2108 B hB hF
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm486, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2108, h2113, h2115, h2266, h3584, h4084, reducedSource406] using sourceEq486 B hB

theorem rowSound406 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row406 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck406, numericCheck406, reducedZero406 B hB hF, mul_zero]

theorem reducedZero407 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource407 (mixedVector B) = 0 := by
  have h2108 : mixedVector B (Sum.inr 2108) = Sparse.eval nodeValue2108 (mixedVector B) := by
    change mixedMoment B node2108 node2108Labels = _
    exact sound2108 B hB hF
  have h2883 : mixedVector B (Sum.inr 2883) = Sparse.eval nodeValue2883 (mixedVector B) := by
    change mixedMoment B node2883 node2883Labels = _
    exact sound2883 B hB hF
  have h3504 : mixedVector B (Sum.inr 3504) = Sparse.eval nodeValue3504 (mixedVector B) := by
    change mixedMoment B node3504 node3504Labels = _
    exact sound3504 B hB hF
  have h3577 : mixedVector B (Sum.inr 3577) = Sparse.eval nodeValue3577 (mixedVector B) := by
    change mixedMoment B node3577 node3577Labels = _
    exact sound3577 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm487, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2108, h2883, h3504, h3577, h3580, h3584, h4084, reducedSource407] using sourceEq487 B hB

theorem rowSound407 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row407 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck407, numericCheck407, reducedZero407 B hB hF, mul_zero]

theorem reducedZero408 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource408 (mixedVector B) = 0 := by
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2887 : mixedVector B (Sum.inr 2887) = Sparse.eval nodeValue2887 (mixedVector B) := by
    change mixedMoment B node2887 node2887Labels = _
    exact sound2887 B hB hF
  have h3157 : mixedVector B (Sum.inr 3157) = Sparse.eval nodeValue3157 (mixedVector B) := by
    change mixedMoment B node3157 node3157Labels = _
    exact sound3157 B hB hF
  have h3161 : mixedVector B (Sum.inr 3161) = Sparse.eval nodeValue3161 (mixedVector B) := by
    change mixedMoment B node3161 node3161Labels = _
    exact sound3161 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm488, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2113, h2887, h3157, h3161, h3584, h4084, reducedSource408] using sourceEq488 B hB

theorem rowSound408 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row408 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck408, numericCheck408, reducedZero408 B hB hF, mul_zero]

theorem reducedZero409 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource409 (mixedVector B) = 0 := by
  have h2883 : mixedVector B (Sum.inr 2883) = Sparse.eval nodeValue2883 (mixedVector B) := by
    change mixedMoment B node2883 node2883Labels = _
    exact sound2883 B hB hF
  have h2887 : mixedVector B (Sum.inr 2887) = Sparse.eval nodeValue2887 (mixedVector B) := by
    change mixedMoment B node2887 node2887Labels = _
    exact sound2887 B hB hF
  have h2888 : mixedVector B (Sum.inr 2888) = Sparse.eval nodeValue2888 (mixedVector B) := by
    change mixedMoment B node2888 node2888Labels = _
    exact sound2888 B hB hF
  have h3056 : mixedVector B (Sum.inr 3056) = Sparse.eval nodeValue3056 (mixedVector B) := by
    change mixedMoment B node3056 node3056Labels = _
    exact sound3056 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm489, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2883, h2887, h2888, h3056, h3584, h4084, reducedSource409] using sourceEq489 B hB

theorem rowSound409 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row409 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck409, numericCheck409, reducedZero409 B hB hF, mul_zero]

theorem reducedZero410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource410 (mixedVector B) = 0 := by
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h3056 : mixedVector B (Sum.inr 3056) = Sparse.eval nodeValue3056 (mixedVector B) := by
    change mixedMoment B node3056 node3056Labels = _
    exact sound3056 B hB hF
  have h3506 : mixedVector B (Sum.inr 3506) = Sparse.eval nodeValue3506 (mixedVector B) := by
    change mixedMoment B node3506 node3506Labels = _
    exact sound3506 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm490, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2115, h3056, h3506, h3582, h3584, h4084, reducedSource410] using sourceEq490 B hB

theorem rowSound410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row410 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck410, numericCheck410, reducedZero410 B hB hF, mul_zero]

theorem reducedZero411 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource411 (mixedVector B) = 0 := by
  have h4475 : mixedVector B (Sum.inr 4475) = Sparse.eval nodeValue4475 (mixedVector B) := by
    change mixedMoment B node4475 node4475Labels = _
    exact sound4475 B hB hF
  have h4476 : mixedVector B (Sum.inr 4476) = Sparse.eval nodeValue4476 (mixedVector B) := by
    change mixedMoment B node4476 node4476Labels = _
    exact sound4476 B hB hF
  have h4480 : mixedVector B (Sum.inr 4480) = Sparse.eval nodeValue4480 (mixedVector B) := by
    change mixedMoment B node4480 node4480Labels = _
    exact sound4480 B hB hF
  have h4500 : mixedVector B (Sum.inr 4500) = Sparse.eval nodeValue4500 (mixedVector B) := by
    change mixedMoment B node4500 node4500Labels = _
    exact sound4500 B hB hF
  have h5086 : mixedVector B (Sum.inr 5086) = Sparse.eval nodeValue5086 (mixedVector B) := by
    change mixedMoment B node5086 node5086Labels = _
    exact sound5086 B hB hF
  have h5087 : mixedVector B (Sum.inr 5087) = Sparse.eval nodeValue5087 (mixedVector B) := by
    change mixedMoment B node5087 node5087Labels = _
    exact sound5087 B hB hF
  have h5090 : mixedVector B (Sum.inr 5090) = Sparse.eval nodeValue5090 (mixedVector B) := by
    change mixedMoment B node5090 node5090Labels = _
    exact sound5090 B hB hF
  have h5103 : mixedVector B (Sum.inr 5103) = Sparse.eval nodeValue5103 (mixedVector B) := by
    change mixedMoment B node5103 node5103Labels = _
    exact sound5103 B hB hF
  have h5109 : mixedVector B (Sum.inr 5109) = Sparse.eval nodeValue5109 (mixedVector B) := by
    change mixedMoment B node5109 node5109Labels = _
    exact sound5109 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  have h5207 : mixedVector B (Sum.inr 5207) = Sparse.eval nodeValue5207 (mixedVector B) := by
    change mixedMoment B node5207 node5207Labels = _
    exact sound5207 B hB hF
  have h5267 : mixedVector B (Sum.inr 5267) = Sparse.eval nodeValue5267 (mixedVector B) := by
    change mixedMoment B node5267 node5267Labels = _
    exact sound5267 B hB hF
  have h5268 : mixedVector B (Sum.inr 5268) = Sparse.eval nodeValue5268 (mixedVector B) := by
    change mixedMoment B node5268 node5268Labels = _
    exact sound5268 B hB hF
  have h5276 : mixedVector B (Sum.inr 5276) = Sparse.eval nodeValue5276 (mixedVector B) := by
    change mixedMoment B node5276 node5276Labels = _
    exact sound5276 B hB hF
  have h5295 : mixedVector B (Sum.inr 5295) = Sparse.eval nodeValue5295 (mixedVector B) := by
    change mixedMoment B node5295 node5295Labels = _
    exact sound5295 B hB hF
  have h5299 : mixedVector B (Sum.inr 5299) = Sparse.eval nodeValue5299 (mixedVector B) := by
    change mixedMoment B node5299 node5299Labels = _
    exact sound5299 B hB hF
  have h5300 : mixedVector B (Sum.inr 5300) = Sparse.eval nodeValue5300 (mixedVector B) := by
    change mixedMoment B node5300 node5300Labels = _
    exact sound5300 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5413 : mixedVector B (Sum.inr 5413) = Sparse.eval nodeValue5413 (mixedVector B) := by
    change mixedMoment B node5413 node5413Labels = _
    exact sound5413 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  simpa only [sourceForm493, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4475, h4476, h4480, h4500, h5086, h5087, h5090, h5103, h5109, h5204, h5207, h5267, h5268, h5276, h5295, h5299, h5300, h5411, h5413, h5443, h5451, reducedSource411] using sourceEq493 B hB

theorem rowSound411 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row411 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck411, numericCheck411, reducedZero411 B hB hF, mul_zero]

theorem reducedZero412 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource412 (mixedVector B) = 0 := by
  have h1058 : mixedVector B (Sum.inr 1058) = Sparse.eval nodeValue1058 (mixedVector B) := by
    change mixedMoment B node1058 node1058Labels = _
    exact sound1058 B hB hF
  have h1059 : mixedVector B (Sum.inr 1059) = Sparse.eval nodeValue1059 (mixedVector B) := by
    change mixedMoment B node1059 node1059Labels = _
    exact sound1059 B hB hF
  have h1063 : mixedVector B (Sum.inr 1063) = Sparse.eval nodeValue1063 (mixedVector B) := by
    change mixedMoment B node1063 node1063Labels = _
    exact sound1063 B hB hF
  have h1084 : mixedVector B (Sum.inr 1084) = Sparse.eval nodeValue1084 (mixedVector B) := by
    change mixedMoment B node1084 node1084Labels = _
    exact sound1084 B hB hF
  have h2494 : mixedVector B (Sum.inr 2494) = Sparse.eval nodeValue2494 (mixedVector B) := by
    change mixedMoment B node2494 node2494Labels = _
    exact sound2494 B hB hF
  have h2495 : mixedVector B (Sum.inr 2495) = Sparse.eval nodeValue2495 (mixedVector B) := by
    change mixedMoment B node2495 node2495Labels = _
    exact sound2495 B hB hF
  have h2499 : mixedVector B (Sum.inr 2499) = Sparse.eval nodeValue2499 (mixedVector B) := by
    change mixedMoment B node2499 node2499Labels = _
    exact sound2499 B hB hF
  have h2513 : mixedVector B (Sum.inr 2513) = Sparse.eval nodeValue2513 (mixedVector B) := by
    change mixedMoment B node2513 node2513Labels = _
    exact sound2513 B hB hF
  have h2638 : mixedVector B (Sum.inr 2638) = Sparse.eval nodeValue2638 (mixedVector B) := by
    change mixedMoment B node2638 node2638Labels = _
    exact sound2638 B hB hF
  have h2640 : mixedVector B (Sum.inr 2640) = Sparse.eval nodeValue2640 (mixedVector B) := by
    change mixedMoment B node2640 node2640Labels = _
    exact sound2640 B hB hF
  have h2644 : mixedVector B (Sum.inr 2644) = Sparse.eval nodeValue2644 (mixedVector B) := by
    change mixedMoment B node2644 node2644Labels = _
    exact sound2644 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h3883 : mixedVector B (Sum.inr 3883) = Sparse.eval nodeValue3883 (mixedVector B) := by
    change mixedMoment B node3883 node3883Labels = _
    exact sound3883 B hB hF
  have h3888 : mixedVector B (Sum.inr 3888) = Sparse.eval nodeValue3888 (mixedVector B) := by
    change mixedMoment B node3888 node3888Labels = _
    exact sound3888 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  have h4006 : mixedVector B (Sum.inr 4006) = Sparse.eval nodeValue4006 (mixedVector B) := by
    change mixedMoment B node4006 node4006Labels = _
    exact sound4006 B hB hF
  simpa only [sourceForm494, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1058, h1059, h1063, h1084, h2494, h2495, h2499, h2513, h2638, h2640, h2644, h2732, h2734, h2744, h2773, h2774, h2781, h3883, h3888, h3889, h4006, reducedSource412] using sourceEq494 B hB

theorem rowSound412 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row412 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck412, numericCheck412, reducedZero412 B hB hF, mul_zero]

theorem reducedZero413 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource413 (mixedVector B) = 0 := by
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h1740 : mixedVector B (Sum.inr 1740) = Sparse.eval nodeValue1740 (mixedVector B) := by
    change mixedMoment B node1740 node1740Labels = _
    exact sound1740 B hB hF
  have h3024 : mixedVector B (Sum.inr 3024) = Sparse.eval nodeValue3024 (mixedVector B) := by
    change mixedMoment B node3024 node3024Labels = _
    exact sound3024 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3464 : mixedVector B (Sum.inr 3464) = Sparse.eval nodeValue3464 (mixedVector B) := by
    change mixedMoment B node3464 node3464Labels = _
    exact sound3464 B hB hF
  have h3472 : mixedVector B (Sum.inr 3472) = Sparse.eval nodeValue3472 (mixedVector B) := by
    change mixedMoment B node3472 node3472Labels = _
    exact sound3472 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h3486 : mixedVector B (Sum.inr 3486) = Sparse.eval nodeValue3486 (mixedVector B) := by
    change mixedMoment B node3486 node3486Labels = _
    exact sound3486 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3624 : mixedVector B (Sum.inr 3624) = Sparse.eval nodeValue3624 (mixedVector B) := by
    change mixedMoment B node3624 node3624Labels = _
    exact sound3624 B hB hF
  have h3631 : mixedVector B (Sum.inr 3631) = Sparse.eval nodeValue3631 (mixedVector B) := by
    change mixedMoment B node3631 node3631Labels = _
    exact sound3631 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3817 : mixedVector B (Sum.inr 3817) = Sparse.eval nodeValue3817 (mixedVector B) := by
    change mixedMoment B node3817 node3817Labels = _
    exact sound3817 B hB hF
  have h3862 : mixedVector B (Sum.inr 3862) = Sparse.eval nodeValue3862 (mixedVector B) := by
    change mixedMoment B node3862 node3862Labels = _
    exact sound3862 B hB hF
  have h3987 : mixedVector B (Sum.inr 3987) = Sparse.eval nodeValue3987 (mixedVector B) := by
    change mixedMoment B node3987 node3987Labels = _
    exact sound3987 B hB hF
  simpa only [sourceForm495, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1715, h1716, h1729, h1740, h3024, h3052, h3098, h3464, h3472, h3480, h3486, h3541, h3549, h3573, h3584, h3624, h3631, h3809, h3817, h3862, h3987, reducedSource413] using sourceEq495 B hB

theorem rowSound413 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row413 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck413, numericCheck413, reducedZero413 B hB hF, mul_zero]

theorem reducedZero414 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource414 (mixedVector B) = 0 := by
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3817 : mixedVector B (Sum.inr 3817) = Sparse.eval nodeValue3817 (mixedVector B) := by
    change mixedMoment B node3817 node3817Labels = _
    exact sound3817 B hB hF
  have h3907 : mixedVector B (Sum.inr 3907) = Sparse.eval nodeValue3907 (mixedVector B) := by
    change mixedMoment B node3907 node3907Labels = _
    exact sound3907 B hB hF
  have h3913 : mixedVector B (Sum.inr 3913) = Sparse.eval nodeValue3913 (mixedVector B) := by
    change mixedMoment B node3913 node3913Labels = _
    exact sound3913 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm496, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3054, h3813, h3817, h3907, h3913, h4092, reducedSource414] using sourceEq496 B hB

theorem rowSound414 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row414 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck414, numericCheck414, reducedZero414 B hB hF, mul_zero]

theorem reducedZero415 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource415 (mixedVector B) = 0 := by
  have h1367 : mixedVector B (Sum.inr 1367) = Sparse.eval nodeValue1367 (mixedVector B) := by
    change mixedMoment B node1367 node1367Labels = _
    exact sound1367 B hB hF
  have h1372 : mixedVector B (Sum.inr 1372) = Sparse.eval nodeValue1372 (mixedVector B) := by
    change mixedMoment B node1372 node1372Labels = _
    exact sound1372 B hB hF
  have h1375 : mixedVector B (Sum.inr 1375) = Sparse.eval nodeValue1375 (mixedVector B) := by
    change mixedMoment B node1375 node1375Labels = _
    exact sound1375 B hB hF
  have h1436 : mixedVector B (Sum.inr 1436) = Sparse.eval nodeValue1436 (mixedVector B) := by
    change mixedMoment B node1436 node1436Labels = _
    exact sound1436 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm497, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1367, h1372, h1375, h1436, h3054, h4092, reducedSource415] using sourceEq497 B hB

theorem rowSound415 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row415 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck415, numericCheck415, reducedZero415 B hB hF, mul_zero]

theorem sourceRowsAt400 : MixedData.sourceRows (400 : Fin 2425) =
    MixedData.row400 := by decide +kernel

theorem sourceRowsAt401 : MixedData.sourceRows (401 : Fin 2425) =
    MixedData.row401 := by decide +kernel

theorem sourceRowsAt402 : MixedData.sourceRows (402 : Fin 2425) =
    MixedData.row402 := by decide +kernel

theorem sourceRowsAt403 : MixedData.sourceRows (403 : Fin 2425) =
    MixedData.row403 := by decide +kernel

theorem sourceRowsAt404 : MixedData.sourceRows (404 : Fin 2425) =
    MixedData.row404 := by decide +kernel

theorem sourceRowsAt405 : MixedData.sourceRows (405 : Fin 2425) =
    MixedData.row405 := by decide +kernel

theorem sourceRowsAt406 : MixedData.sourceRows (406 : Fin 2425) =
    MixedData.row406 := by decide +kernel

theorem sourceRowsAt407 : MixedData.sourceRows (407 : Fin 2425) =
    MixedData.row407 := by decide +kernel

theorem sourceRowsAt408 : MixedData.sourceRows (408 : Fin 2425) =
    MixedData.row408 := by decide +kernel

theorem sourceRowsAt409 : MixedData.sourceRows (409 : Fin 2425) =
    MixedData.row409 := by decide +kernel

theorem sourceRowsAt410 : MixedData.sourceRows (410 : Fin 2425) =
    MixedData.row410 := by decide +kernel

theorem sourceRowsAt411 : MixedData.sourceRows (411 : Fin 2425) =
    MixedData.row411 := by decide +kernel

theorem sourceRowsAt412 : MixedData.sourceRows (412 : Fin 2425) =
    MixedData.row412 := by decide +kernel

theorem sourceRowsAt413 : MixedData.sourceRows (413 : Fin 2425) =
    MixedData.row413 := by decide +kernel

theorem sourceRowsAt414 : MixedData.sourceRows (414 : Fin 2425) =
    MixedData.row414 := by decide +kernel

theorem sourceRowsAt415 : MixedData.sourceRows (415 : Fin 2425) =
    MixedData.row415 := by decide +kernel

theorem chunkSound25 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 25) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 400 ∨ k.val = 401 ∨ k.val = 402 ∨ k.val = 403 ∨ k.val = 404 ∨ k.val = 405 ∨ k.val = 406 ∨ k.val = 407 ∨ k.val = 408 ∨ k.val = 409 ∨ k.val = 410 ∨ k.val = 411 ∨ k.val = 412 ∨ k.val = 413 ∨ k.val = 414 ∨ k.val = 415 := by omega
  rcases heq with h400 | h401 | h402 | h403 | h404 | h405 | h406 | h407 | h408 | h409 | h410 | h411 | h412 | h413 | h414 | h415
  · have he : k = (400 : Fin 2425) := Fin.ext h400
    subst k
    rw [sourceRowsAt400]
    exact rowSound400 B hB hF
  · have he : k = (401 : Fin 2425) := Fin.ext h401
    subst k
    rw [sourceRowsAt401]
    exact rowSound401 B hB hF
  · have he : k = (402 : Fin 2425) := Fin.ext h402
    subst k
    rw [sourceRowsAt402]
    exact rowSound402 B hB hF
  · have he : k = (403 : Fin 2425) := Fin.ext h403
    subst k
    rw [sourceRowsAt403]
    exact rowSound403 B hB hF
  · have he : k = (404 : Fin 2425) := Fin.ext h404
    subst k
    rw [sourceRowsAt404]
    exact rowSound404 B hB hF
  · have he : k = (405 : Fin 2425) := Fin.ext h405
    subst k
    rw [sourceRowsAt405]
    exact rowSound405 B hB hF
  · have he : k = (406 : Fin 2425) := Fin.ext h406
    subst k
    rw [sourceRowsAt406]
    exact rowSound406 B hB hF
  · have he : k = (407 : Fin 2425) := Fin.ext h407
    subst k
    rw [sourceRowsAt407]
    exact rowSound407 B hB hF
  · have he : k = (408 : Fin 2425) := Fin.ext h408
    subst k
    rw [sourceRowsAt408]
    exact rowSound408 B hB hF
  · have he : k = (409 : Fin 2425) := Fin.ext h409
    subst k
    rw [sourceRowsAt409]
    exact rowSound409 B hB hF
  · have he : k = (410 : Fin 2425) := Fin.ext h410
    subst k
    rw [sourceRowsAt410]
    exact rowSound410 B hB hF
  · have he : k = (411 : Fin 2425) := Fin.ext h411
    subst k
    rw [sourceRowsAt411]
    exact rowSound411 B hB hF
  · have he : k = (412 : Fin 2425) := Fin.ext h412
    subst k
    rw [sourceRowsAt412]
    exact rowSound412 B hB hF
  · have he : k = (413 : Fin 2425) := Fin.ext h413
    subst k
    rw [sourceRowsAt413]
    exact rowSound413 B hB hF
  · have he : k = (414 : Fin 2425) := Fin.ext h414
    subst k
    rw [sourceRowsAt414]
    exact rowSound414 B hB hF
  · have he : k = (415 : Fin 2425) := Fin.ext h415
    subst k
    rw [sourceRowsAt415]
    exact rowSound415 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
