import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources14

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero384 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource384 (mixedVector B) = 0 := by
  have h2090 : mixedVector B (Sum.inr 2090) = Sparse.eval nodeValue2090 (mixedVector B) := by
    change mixedMoment B node2090 node2090Labels = _
    exact sound2090 B hB hF
  have h2962 : mixedVector B (Sum.inr 2962) = Sparse.eval nodeValue2962 (mixedVector B) := by
    change mixedMoment B node2962 node2962Labels = _
    exact sound2962 B hB hF
  have h2983 : mixedVector B (Sum.inr 2983) = Sparse.eval nodeValue2983 (mixedVector B) := by
    change mixedMoment B node2983 node2983Labels = _
    exact sound2983 B hB hF
  have h2995 : mixedVector B (Sum.inr 2995) = Sparse.eval nodeValue2995 (mixedVector B) := by
    change mixedMoment B node2995 node2995Labels = _
    exact sound2995 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm455, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2090, h2962, h2983, h2995, h3098, h3572, h4083, reducedSource384] using sourceEq455 B hB

theorem rowSound384 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row384 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck384, numericCheck384, reducedZero384 B hB hF, mul_zero]

theorem reducedZero385 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource385 (mixedVector B) = 0 := by
  have h1440 : mixedVector B (Sum.inr 1440) = Sparse.eval nodeValue1440 (mixedVector B) := by
    change mixedMoment B node1440 node1440Labels = _
    exact sound1440 B hB hF
  have h2995 : mixedVector B (Sum.inr 2995) = Sparse.eval nodeValue2995 (mixedVector B) := by
    change mixedMoment B node2995 node2995Labels = _
    exact sound2995 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3118 : mixedVector B (Sum.inr 3118) = Sparse.eval nodeValue3118 (mixedVector B) := by
    change mixedMoment B node3118 node3118Labels = _
    exact sound3118 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm456, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1440, h2995, h3098, h3118, h4083, reducedSource385] using sourceEq456 B hB

theorem rowSound385 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row385 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck385, numericCheck385, reducedZero385 B hB hF, mul_zero]

theorem reducedZero386 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource386 (mixedVector B) = 0 := by
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h2967 : mixedVector B (Sum.inr 2967) = Sparse.eval nodeValue2967 (mixedVector B) := by
    change mixedMoment B node2967 node2967Labels = _
    exact sound2967 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm457, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2112, h2952, h2967, h3098, h3583, h4083, reducedSource386] using sourceEq457 B hB

theorem rowSound386 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row386 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck386, numericCheck386, reducedZero386 B hB hF, mul_zero]

theorem reducedZero387 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource387 (mixedVector B) = 0 := by
  have h1418 : mixedVector B (Sum.inr 1418) = Sparse.eval nodeValue1418 (mixedVector B) := by
    change mixedMoment B node1418 node1418Labels = _
    exact sound1418 B hB hF
  have h2962 : mixedVector B (Sum.inr 2962) = Sparse.eval nodeValue2962 (mixedVector B) := by
    change mixedMoment B node2962 node2962Labels = _
    exact sound2962 B hB hF
  have h2967 : mixedVector B (Sum.inr 2967) = Sparse.eval nodeValue2967 (mixedVector B) := by
    change mixedMoment B node2967 node2967Labels = _
    exact sound2967 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm458, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1418, h2962, h2967, h3098, h4083, reducedSource387] using sourceEq458 B hB

theorem rowSound387 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row387 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck387, numericCheck387, reducedZero387 B hB hF, mul_zero]

theorem reducedZero388 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource388 (mixedVector B) = 0 := by
  have h2516 : mixedVector B (Sum.inr 2516) = Sparse.eval nodeValue2516 (mixedVector B) := by
    change mixedMoment B node2516 node2516Labels = _
    exact sound2516 B hB hF
  have h2520 : mixedVector B (Sum.inr 2520) = Sparse.eval nodeValue2520 (mixedVector B) := by
    change mixedMoment B node2520 node2520Labels = _
    exact sound2520 B hB hF
  have h2521 : mixedVector B (Sum.inr 2521) = Sparse.eval nodeValue2521 (mixedVector B) := by
    change mixedMoment B node2521 node2521Labels = _
    exact sound2521 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  have h2789 : mixedVector B (Sum.inr 2789) = Sparse.eval nodeValue2789 (mixedVector B) := by
    change mixedMoment B node2789 node2789Labels = _
    exact sound2789 B hB hF
  have h3035 : mixedVector B (Sum.inr 3035) = Sparse.eval nodeValue3035 (mixedVector B) := by
    change mixedMoment B node3035 node3035Labels = _
    exact sound3035 B hB hF
  have h3049 : mixedVector B (Sum.inr 3049) = Sparse.eval nodeValue3049 (mixedVector B) := by
    change mixedMoment B node3049 node3049Labels = _
    exact sound3049 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3063 : mixedVector B (Sum.inr 3063) = Sparse.eval nodeValue3063 (mixedVector B) := by
    change mixedMoment B node3063 node3063Labels = _
    exact sound3063 B hB hF
  have h3072 : mixedVector B (Sum.inr 3072) = Sparse.eval nodeValue3072 (mixedVector B) := by
    change mixedMoment B node3072 node3072Labels = _
    exact sound3072 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3121 : mixedVector B (Sum.inr 3121) = Sparse.eval nodeValue3121 (mixedVector B) := by
    change mixedMoment B node3121 node3121Labels = _
    exact sound3121 B hB hF
  have h3158 : mixedVector B (Sum.inr 3158) = Sparse.eval nodeValue3158 (mixedVector B) := by
    change mixedMoment B node3158 node3158Labels = _
    exact sound3158 B hB hF
  have h3161 : mixedVector B (Sum.inr 3161) = Sparse.eval nodeValue3161 (mixedVector B) := by
    change mixedMoment B node3161 node3161Labels = _
    exact sound3161 B hB hF
  have h3225 : mixedVector B (Sum.inr 3225) = Sparse.eval nodeValue3225 (mixedVector B) := by
    change mixedMoment B node3225 node3225Labels = _
    exact sound3225 B hB hF
  simpa only [sourceForm461, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2516, h2520, h2521, h2719, h2737, h2740, h2783, h2789, h3035, h3049, h3052, h3063, h3072, h3075, h3086, h3098, h3101, h3121, h3158, h3161, h3225, reducedSource388] using sourceEq461 B hB

theorem rowSound388 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row388 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck388, numericCheck388, reducedZero388 B hB hF, mul_zero]

theorem reducedZero389 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource389 (mixedVector B) = 0 := by
  have h1292 : mixedVector B (Sum.inr 1292) = Sparse.eval nodeValue1292 (mixedVector B) := by
    change mixedMoment B node1292 node1292Labels = _
    exact sound1292 B hB hF
  have h2588 : mixedVector B (Sum.inr 2588) = Sparse.eval nodeValue2588 (mixedVector B) := by
    change mixedMoment B node2588 node2588Labels = _
    exact sound2588 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm462, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1292, h2588, h2740, h2781, h2783, h4084, reducedSource389] using sourceEq462 B hB

theorem rowSound389 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row389 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck389, numericCheck389, reducedZero389 B hB hF, mul_zero]

theorem reducedZero390 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource390 (mixedVector B) = 0 := by
  have h2132 : mixedVector B (Sum.inr 2132) = Sparse.eval nodeValue2132 (mixedVector B) := by
    change mixedMoment B node2132 node2132Labels = _
    exact sound2132 B hB hF
  have h2134 : mixedVector B (Sum.inr 2134) = Sparse.eval nodeValue2134 (mixedVector B) := by
    change mixedMoment B node2134 node2134Labels = _
    exact sound2134 B hB hF
  have h2138 : mixedVector B (Sum.inr 2138) = Sparse.eval nodeValue2138 (mixedVector B) := by
    change mixedMoment B node2138 node2138Labels = _
    exact sound2138 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm463, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2132, h2134, h2138, h2278, h2781, h4084, reducedSource390] using sourceEq463 B hB

theorem rowSound390 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row390 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck390, numericCheck390, reducedZero390 B hB hF, mul_zero]

theorem reducedZero391 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource391 (mixedVector B) = 0 := by
  have h1189 : mixedVector B (Sum.inr 1189) = Sparse.eval nodeValue1189 (mixedVector B) := by
    change mixedMoment B node1189 node1189Labels = _
    exact sound1189 B hB hF
  have h1191 : mixedVector B (Sum.inr 1191) = Sparse.eval nodeValue1191 (mixedVector B) := by
    change mixedMoment B node1191 node1191Labels = _
    exact sound1191 B hB hF
  have h1192 : mixedVector B (Sum.inr 1192) = Sparse.eval nodeValue1192 (mixedVector B) := by
    change mixedMoment B node1192 node1192Labels = _
    exact sound1192 B hB hF
  have h1295 : mixedVector B (Sum.inr 1295) = Sparse.eval nodeValue1295 (mixedVector B) := by
    change mixedMoment B node1295 node1295Labels = _
    exact sound1295 B hB hF
  have h2393 : mixedVector B (Sum.inr 2393) = Sparse.eval nodeValue2393 (mixedVector B) := by
    change mixedMoment B node2393 node2393Labels = _
    exact sound2393 B hB hF
  have h2408 : mixedVector B (Sum.inr 2408) = Sparse.eval nodeValue2408 (mixedVector B) := by
    change mixedMoment B node2408 node2408Labels = _
    exact sound2408 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2841 : mixedVector B (Sum.inr 2841) = Sparse.eval nodeValue2841 (mixedVector B) := by
    change mixedMoment B node2841 node2841Labels = _
    exact sound2841 B hB hF
  have h2842 : mixedVector B (Sum.inr 2842) = Sparse.eval nodeValue2842 (mixedVector B) := by
    change mixedMoment B node2842 node2842Labels = _
    exact sound2842 B hB hF
  have h2909 : mixedVector B (Sum.inr 2909) = Sparse.eval nodeValue2909 (mixedVector B) := by
    change mixedMoment B node2909 node2909Labels = _
    exact sound2909 B hB hF
  have h2910 : mixedVector B (Sum.inr 2910) = Sparse.eval nodeValue2910 (mixedVector B) := by
    change mixedMoment B node2910 node2910Labels = _
    exact sound2910 B hB hF
  have h2955 : mixedVector B (Sum.inr 2955) = Sparse.eval nodeValue2955 (mixedVector B) := by
    change mixedMoment B node2955 node2955Labels = _
    exact sound2955 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3110 : mixedVector B (Sum.inr 3110) = Sparse.eval nodeValue3110 (mixedVector B) := by
    change mixedMoment B node3110 node3110Labels = _
    exact sound3110 B hB hF
  have h3119 : mixedVector B (Sum.inr 3119) = Sparse.eval nodeValue3119 (mixedVector B) := by
    change mixedMoment B node3119 node3119Labels = _
    exact sound3119 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3862 : mixedVector B (Sum.inr 3862) = Sparse.eval nodeValue3862 (mixedVector B) := by
    change mixedMoment B node3862 node3862Labels = _
    exact sound3862 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  simpa only [sourceForm466, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1189, h1191, h1192, h1295, h2393, h2408, h2734, h2841, h2842, h2909, h2910, h2955, h3039, h3051, h3052, h3110, h3119, h3584, h3862, h3877, h3889, reducedSource391] using sourceEq466 B hB

theorem rowSound391 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row391 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck391, numericCheck391, reducedZero391 B hB hF, mul_zero]

theorem reducedZero392 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource392 (mixedVector B) = 0 := by
  have h2405 : mixedVector B (Sum.inr 2405) = Sparse.eval nodeValue2405 (mixedVector B) := by
    change mixedMoment B node2405 node2405Labels = _
    exact sound2405 B hB hF
  have h2408 : mixedVector B (Sum.inr 2408) = Sparse.eval nodeValue2408 (mixedVector B) := by
    change mixedMoment B node2408 node2408Labels = _
    exact sound2408 B hB hF
  have h2409 : mixedVector B (Sum.inr 2409) = Sparse.eval nodeValue2409 (mixedVector B) := by
    change mixedMoment B node2409 node2409Labels = _
    exact sound2409 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h2841 : mixedVector B (Sum.inr 2841) = Sparse.eval nodeValue2841 (mixedVector B) := by
    change mixedMoment B node2841 node2841Labels = _
    exact sound2841 B hB hF
  have h2842 : mixedVector B (Sum.inr 2842) = Sparse.eval nodeValue2842 (mixedVector B) := by
    change mixedMoment B node2842 node2842Labels = _
    exact sound2842 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3246 : mixedVector B (Sum.inr 3246) = Sparse.eval nodeValue3246 (mixedVector B) := by
    change mixedMoment B node3246 node3246Labels = _
    exact sound3246 B hB hF
  have h3247 : mixedVector B (Sum.inr 3247) = Sparse.eval nodeValue3247 (mixedVector B) := by
    change mixedMoment B node3247 node3247Labels = _
    exact sound3247 B hB hF
  have h3306 : mixedVector B (Sum.inr 3306) = Sparse.eval nodeValue3306 (mixedVector B) := by
    change mixedMoment B node3306 node3306Labels = _
    exact sound3306 B hB hF
  have h3358 : mixedVector B (Sum.inr 3358) = Sparse.eval nodeValue3358 (mixedVector B) := by
    change mixedMoment B node3358 node3358Labels = _
    exact sound3358 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h3559 : mixedVector B (Sum.inr 3559) = Sparse.eval nodeValue3559 (mixedVector B) := by
    change mixedMoment B node3559 node3559Labels = _
    exact sound3559 B hB hF
  have h3565 : mixedVector B (Sum.inr 3565) = Sparse.eval nodeValue3565 (mixedVector B) := by
    change mixedMoment B node3565 node3565Labels = _
    exact sound3565 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h3862 : mixedVector B (Sum.inr 3862) = Sparse.eval nodeValue3862 (mixedVector B) := by
    change mixedMoment B node3862 node3862Labels = _
    exact sound3862 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  simpa only [sourceForm467, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2405, h2408, h2409, h2744, h2841, h2842, h3055, h3246, h3247, h3306, h3358, h3535, h3548, h3549, h3559, h3565, h3573, h3583, h3862, h3877, h3889, reducedSource392] using sourceEq467 B hB

theorem rowSound392 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row392 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck392, numericCheck392, reducedZero392 B hB hF, mul_zero]

theorem reducedZero393 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource393 (mixedVector B) = 0 := by
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h3907 : mixedVector B (Sum.inr 3907) = Sparse.eval nodeValue3907 (mixedVector B) := by
    change mixedMoment B node3907 node3907Labels = _
    exact sound3907 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm468, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2774, h3854, h3907, h4092, reducedSource393] using sourceEq468 B hB

theorem rowSound393 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row393 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck393, numericCheck393, reducedZero393 B hB hF, mul_zero]

theorem reducedZero394 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource394 (mixedVector B) = 0 := by
  have h1295 : mixedVector B (Sum.inr 1295) = Sparse.eval nodeValue1295 (mixedVector B) := by
    change mixedMoment B node1295 node1295Labels = _
    exact sound1295 B hB hF
  have h2591 : mixedVector B (Sum.inr 2591) = Sparse.eval nodeValue2591 (mixedVector B) := by
    change mixedMoment B node2591 node2591Labels = _
    exact sound2591 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm471, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1295, h2591, h2743, h2774, h2782, h4092, reducedSource394] using sourceEq471 B hB

theorem rowSound394 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row394 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck394, numericCheck394, reducedZero394 B hB hF, mul_zero]

theorem reducedZero395 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource395 (mixedVector B) = 0 := by
  have h1054 : mixedVector B (Sum.inr 1054) = Sparse.eval nodeValue1054 (mixedVector B) := by
    change mixedMoment B node1054 node1054Labels = _
    exact sound1054 B hB hF
  have h1055 : mixedVector B (Sum.inr 1055) = Sparse.eval nodeValue1055 (mixedVector B) := by
    change mixedMoment B node1055 node1055Labels = _
    exact sound1055 B hB hF
  have h1063 : mixedVector B (Sum.inr 1063) = Sparse.eval nodeValue1063 (mixedVector B) := by
    change mixedMoment B node1063 node1063Labels = _
    exact sound1063 B hB hF
  have h1076 : mixedVector B (Sum.inr 1076) = Sparse.eval nodeValue1076 (mixedVector B) := by
    change mixedMoment B node1076 node1076Labels = _
    exact sound1076 B hB hF
  have h2491 : mixedVector B (Sum.inr 2491) = Sparse.eval nodeValue2491 (mixedVector B) := by
    change mixedMoment B node2491 node2491Labels = _
    exact sound2491 B hB hF
  have h2492 : mixedVector B (Sum.inr 2492) = Sparse.eval nodeValue2492 (mixedVector B) := by
    change mixedMoment B node2492 node2492Labels = _
    exact sound2492 B hB hF
  have h2499 : mixedVector B (Sum.inr 2499) = Sparse.eval nodeValue2499 (mixedVector B) := by
    change mixedMoment B node2499 node2499Labels = _
    exact sound2499 B hB hF
  have h2506 : mixedVector B (Sum.inr 2506) = Sparse.eval nodeValue2506 (mixedVector B) := by
    change mixedMoment B node2506 node2506Labels = _
    exact sound2506 B hB hF
  have h2633 : mixedVector B (Sum.inr 2633) = Sparse.eval nodeValue2633 (mixedVector B) := by
    change mixedMoment B node2633 node2633Labels = _
    exact sound2633 B hB hF
  have h2635 : mixedVector B (Sum.inr 2635) = Sparse.eval nodeValue2635 (mixedVector B) := by
    change mixedMoment B node2635 node2635Labels = _
    exact sound2635 B hB hF
  have h2644 : mixedVector B (Sum.inr 2644) = Sparse.eval nodeValue2644 (mixedVector B) := by
    change mixedMoment B node2644 node2644Labels = _
    exact sound2644 B hB hF
  have h2678 : mixedVector B (Sum.inr 2678) = Sparse.eval nodeValue2678 (mixedVector B) := by
    change mixedMoment B node2678 node2678Labels = _
    exact sound2678 B hB hF
  have h2680 : mixedVector B (Sum.inr 2680) = Sparse.eval nodeValue2680 (mixedVector B) := by
    change mixedMoment B node2680 node2680Labels = _
    exact sound2680 B hB hF
  have h2687 : mixedVector B (Sum.inr 2687) = Sparse.eval nodeValue2687 (mixedVector B) := by
    change mixedMoment B node2687 node2687Labels = _
    exact sound2687 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2776 : mixedVector B (Sum.inr 2776) = Sparse.eval nodeValue2776 (mixedVector B) := by
    change mixedMoment B node2776 node2776Labels = _
    exact sound2776 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h3886 : mixedVector B (Sum.inr 3886) = Sparse.eval nodeValue3886 (mixedVector B) := by
    change mixedMoment B node3886 node3886Labels = _
    exact sound3886 B hB hF
  have h3888 : mixedVector B (Sum.inr 3888) = Sparse.eval nodeValue3888 (mixedVector B) := by
    change mixedMoment B node3888 node3888Labels = _
    exact sound3888 B hB hF
  have h4004 : mixedVector B (Sum.inr 4004) = Sparse.eval nodeValue4004 (mixedVector B) := by
    change mixedMoment B node4004 node4004Labels = _
    exact sound4004 B hB hF
  simpa only [sourceForm473, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1054, h1055, h1063, h1076, h2491, h2492, h2499, h2506, h2633, h2635, h2644, h2678, h2680, h2687, h2773, h2776, h2781, h3881, h3886, h3888, h4004, reducedSource395] using sourceEq473 B hB

theorem rowSound395 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row395 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck395, numericCheck395, reducedZero395 B hB hF, mul_zero]

theorem reducedZero396 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource396 (mixedVector B) = 0 := by
  have h1649 : mixedVector B (Sum.inr 1649) = Sparse.eval nodeValue1649 (mixedVector B) := by
    change mixedMoment B node1649 node1649Labels = _
    exact sound1649 B hB hF
  have h1651 : mixedVector B (Sum.inr 1651) = Sparse.eval nodeValue1651 (mixedVector B) := by
    change mixedMoment B node1651 node1651Labels = _
    exact sound1651 B hB hF
  have h1652 : mixedVector B (Sum.inr 1652) = Sparse.eval nodeValue1652 (mixedVector B) := by
    change mixedMoment B node1652 node1652Labels = _
    exact sound1652 B hB hF
  have h1740 : mixedVector B (Sum.inr 1740) = Sparse.eval nodeValue1740 (mixedVector B) := by
    change mixedMoment B node1740 node1740Labels = _
    exact sound1740 B hB hF
  have h2875 : mixedVector B (Sum.inr 2875) = Sparse.eval nodeValue2875 (mixedVector B) := by
    change mixedMoment B node2875 node2875Labels = _
    exact sound2875 B hB hF
  have h2888 : mixedVector B (Sum.inr 2888) = Sparse.eval nodeValue2888 (mixedVector B) := by
    change mixedMoment B node2888 node2888Labels = _
    exact sound2888 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3385 : mixedVector B (Sum.inr 3385) = Sparse.eval nodeValue3385 (mixedVector B) := by
    change mixedMoment B node3385 node3385Labels = _
    exact sound3385 B hB hF
  have h3395 : mixedVector B (Sum.inr 3395) = Sparse.eval nodeValue3395 (mixedVector B) := by
    change mixedMoment B node3395 node3395Labels = _
    exact sound3395 B hB hF
  have h3396 : mixedVector B (Sum.inr 3396) = Sparse.eval nodeValue3396 (mixedVector B) := by
    change mixedMoment B node3396 node3396Labels = _
    exact sound3396 B hB hF
  have h3447 : mixedVector B (Sum.inr 3447) = Sparse.eval nodeValue3447 (mixedVector B) := by
    change mixedMoment B node3447 node3447Labels = _
    exact sound3447 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3578 : mixedVector B (Sum.inr 3578) = Sparse.eval nodeValue3578 (mixedVector B) := by
    change mixedMoment B node3578 node3578Labels = _
    exact sound3578 B hB hF
  have h3579 : mixedVector B (Sum.inr 3579) = Sparse.eval nodeValue3579 (mixedVector B) := by
    change mixedMoment B node3579 node3579Labels = _
    exact sound3579 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3631 : mixedVector B (Sum.inr 3631) = Sparse.eval nodeValue3631 (mixedVector B) := by
    change mixedMoment B node3631 node3631Labels = _
    exact sound3631 B hB hF
  have h3959 : mixedVector B (Sum.inr 3959) = Sparse.eval nodeValue3959 (mixedVector B) := by
    change mixedMoment B node3959 node3959Labels = _
    exact sound3959 B hB hF
  have h3963 : mixedVector B (Sum.inr 3963) = Sparse.eval nodeValue3963 (mixedVector B) := by
    change mixedMoment B node3963 node3963Labels = _
    exact sound3963 B hB hF
  have h3987 : mixedVector B (Sum.inr 3987) = Sparse.eval nodeValue3987 (mixedVector B) := by
    change mixedMoment B node3987 node3987Labels = _
    exact sound3987 B hB hF
  have h4030 : mixedVector B (Sum.inr 4030) = Sparse.eval nodeValue4030 (mixedVector B) := by
    change mixedMoment B node4030 node4030Labels = _
    exact sound4030 B hB hF
  simpa only [sourceForm474, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1649, h1651, h1652, h1740, h2875, h2888, h3098, h3385, h3395, h3396, h3447, h3480, h3573, h3578, h3579, h3626, h3631, h3959, h3963, h3987, h4030, reducedSource396] using sourceEq474 B hB

theorem rowSound396 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row396 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck396, numericCheck396, reducedZero396 B hB hF, mul_zero]

theorem reducedZero397 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource397 (mixedVector B) = 0 := by
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h3886 : mixedVector B (Sum.inr 3886) = Sparse.eval nodeValue3886 (mixedVector B) := by
    change mixedMoment B node3886 node3886Labels = _
    exact sound3886 B hB hF
  have h3913 : mixedVector B (Sum.inr 3913) = Sparse.eval nodeValue3913 (mixedVector B) := by
    change mixedMoment B node3913 node3913Labels = _
    exact sound3913 B hB hF
  have h3963 : mixedVector B (Sum.inr 3963) = Sparse.eval nodeValue3963 (mixedVector B) := by
    change mixedMoment B node3963 node3963Labels = _
    exact sound3963 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm475, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3055, h3884, h3886, h3913, h3963, h4092, reducedSource397] using sourceEq475 B hB

theorem rowSound397 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row397 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck397, numericCheck397, reducedZero397 B hB hF, mul_zero]

theorem reducedZero398 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource398 (mixedVector B) = 0 := by
  have h1368 : mixedVector B (Sum.inr 1368) = Sparse.eval nodeValue1368 (mixedVector B) := by
    change mixedMoment B node1368 node1368Labels = _
    exact sound1368 B hB hF
  have h1373 : mixedVector B (Sum.inr 1373) = Sparse.eval nodeValue1373 (mixedVector B) := by
    change mixedMoment B node1373 node1373Labels = _
    exact sound1373 B hB hF
  have h1375 : mixedVector B (Sum.inr 1375) = Sparse.eval nodeValue1375 (mixedVector B) := by
    change mixedMoment B node1375 node1375Labels = _
    exact sound1375 B hB hF
  have h1437 : mixedVector B (Sum.inr 1437) = Sparse.eval nodeValue1437 (mixedVector B) := by
    change mixedMoment B node1437 node1437Labels = _
    exact sound1437 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm476, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1368, h1373, h1375, h1437, h3055, h4092, reducedSource398] using sourceEq476 B hB

theorem rowSound398 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row398 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck398, numericCheck398, reducedZero398 B hB hF, mul_zero]

theorem reducedZero399 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource399 (mixedVector B) = 0 := by
  have h1368 : mixedVector B (Sum.inr 1368) = Sparse.eval nodeValue1368 (mixedVector B) := by
    change mixedMoment B node1368 node1368Labels = _
    exact sound1368 B hB hF
  have h2882 : mixedVector B (Sum.inr 2882) = Sparse.eval nodeValue2882 (mixedVector B) := by
    change mixedMoment B node2882 node2882Labels = _
    exact sound2882 B hB hF
  have h2975 : mixedVector B (Sum.inr 2975) = Sparse.eval nodeValue2975 (mixedVector B) := by
    change mixedMoment B node2975 node2975Labels = _
    exact sound2975 B hB hF
  have h3044 : mixedVector B (Sum.inr 3044) = Sparse.eval nodeValue3044 (mixedVector B) := by
    change mixedMoment B node3044 node3044Labels = _
    exact sound3044 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm477, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1368, h2882, h2975, h3044, h3051, h3055, h4092, reducedSource399] using sourceEq477 B hB

theorem rowSound399 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row399 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck399, numericCheck399, reducedZero399 B hB hF, mul_zero]

theorem sourceRowsAt384 : MixedData.sourceRows (384 : Fin 2425) =
    MixedData.row384 := by decide +kernel

theorem sourceRowsAt385 : MixedData.sourceRows (385 : Fin 2425) =
    MixedData.row385 := by decide +kernel

theorem sourceRowsAt386 : MixedData.sourceRows (386 : Fin 2425) =
    MixedData.row386 := by decide +kernel

theorem sourceRowsAt387 : MixedData.sourceRows (387 : Fin 2425) =
    MixedData.row387 := by decide +kernel

theorem sourceRowsAt388 : MixedData.sourceRows (388 : Fin 2425) =
    MixedData.row388 := by decide +kernel

theorem sourceRowsAt389 : MixedData.sourceRows (389 : Fin 2425) =
    MixedData.row389 := by decide +kernel

theorem sourceRowsAt390 : MixedData.sourceRows (390 : Fin 2425) =
    MixedData.row390 := by decide +kernel

theorem sourceRowsAt391 : MixedData.sourceRows (391 : Fin 2425) =
    MixedData.row391 := by decide +kernel

theorem sourceRowsAt392 : MixedData.sourceRows (392 : Fin 2425) =
    MixedData.row392 := by decide +kernel

theorem sourceRowsAt393 : MixedData.sourceRows (393 : Fin 2425) =
    MixedData.row393 := by decide +kernel

theorem sourceRowsAt394 : MixedData.sourceRows (394 : Fin 2425) =
    MixedData.row394 := by decide +kernel

theorem sourceRowsAt395 : MixedData.sourceRows (395 : Fin 2425) =
    MixedData.row395 := by decide +kernel

theorem sourceRowsAt396 : MixedData.sourceRows (396 : Fin 2425) =
    MixedData.row396 := by decide +kernel

theorem sourceRowsAt397 : MixedData.sourceRows (397 : Fin 2425) =
    MixedData.row397 := by decide +kernel

theorem sourceRowsAt398 : MixedData.sourceRows (398 : Fin 2425) =
    MixedData.row398 := by decide +kernel

theorem sourceRowsAt399 : MixedData.sourceRows (399 : Fin 2425) =
    MixedData.row399 := by decide +kernel

theorem chunkSound24 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 24) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 384 ∨ k.val = 385 ∨ k.val = 386 ∨ k.val = 387 ∨ k.val = 388 ∨ k.val = 389 ∨ k.val = 390 ∨ k.val = 391 ∨ k.val = 392 ∨ k.val = 393 ∨ k.val = 394 ∨ k.val = 395 ∨ k.val = 396 ∨ k.val = 397 ∨ k.val = 398 ∨ k.val = 399 := by omega
  rcases heq with h384 | h385 | h386 | h387 | h388 | h389 | h390 | h391 | h392 | h393 | h394 | h395 | h396 | h397 | h398 | h399
  · have he : k = (384 : Fin 2425) := Fin.ext h384
    subst k
    rw [sourceRowsAt384]
    exact rowSound384 B hB hF
  · have he : k = (385 : Fin 2425) := Fin.ext h385
    subst k
    rw [sourceRowsAt385]
    exact rowSound385 B hB hF
  · have he : k = (386 : Fin 2425) := Fin.ext h386
    subst k
    rw [sourceRowsAt386]
    exact rowSound386 B hB hF
  · have he : k = (387 : Fin 2425) := Fin.ext h387
    subst k
    rw [sourceRowsAt387]
    exact rowSound387 B hB hF
  · have he : k = (388 : Fin 2425) := Fin.ext h388
    subst k
    rw [sourceRowsAt388]
    exact rowSound388 B hB hF
  · have he : k = (389 : Fin 2425) := Fin.ext h389
    subst k
    rw [sourceRowsAt389]
    exact rowSound389 B hB hF
  · have he : k = (390 : Fin 2425) := Fin.ext h390
    subst k
    rw [sourceRowsAt390]
    exact rowSound390 B hB hF
  · have he : k = (391 : Fin 2425) := Fin.ext h391
    subst k
    rw [sourceRowsAt391]
    exact rowSound391 B hB hF
  · have he : k = (392 : Fin 2425) := Fin.ext h392
    subst k
    rw [sourceRowsAt392]
    exact rowSound392 B hB hF
  · have he : k = (393 : Fin 2425) := Fin.ext h393
    subst k
    rw [sourceRowsAt393]
    exact rowSound393 B hB hF
  · have he : k = (394 : Fin 2425) := Fin.ext h394
    subst k
    rw [sourceRowsAt394]
    exact rowSound394 B hB hF
  · have he : k = (395 : Fin 2425) := Fin.ext h395
    subst k
    rw [sourceRowsAt395]
    exact rowSound395 B hB hF
  · have he : k = (396 : Fin 2425) := Fin.ext h396
    subst k
    rw [sourceRowsAt396]
    exact rowSound396 B hB hF
  · have he : k = (397 : Fin 2425) := Fin.ext h397
    subst k
    rw [sourceRowsAt397]
    exact rowSound397 B hB hF
  · have he : k = (398 : Fin 2425) := Fin.ext h398
    subst k
    rw [sourceRowsAt398]
    exact rowSound398 B hB hF
  · have he : k = (399 : Fin 2425) := Fin.ext h399
    subst k
    rw [sourceRowsAt399]
    exact rowSound399 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
