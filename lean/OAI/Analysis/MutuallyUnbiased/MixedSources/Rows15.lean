import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources9

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero240 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource240 (mixedVector B) = 0 := by
  have h2973 : mixedVector B (Sum.inr 2973) = Sparse.eval nodeValue2973 (mixedVector B) := by
    change mixedMoment B node2973 node2973Labels = _
    exact sound2973 B hB hF
  have h3490 : mixedVector B (Sum.inr 3490) = Sparse.eval nodeValue3490 (mixedVector B) := by
    change mixedMoment B node3490 node3490Labels = _
    exact sound3490 B hB hF
  have h3494 : mixedVector B (Sum.inr 3494) = Sparse.eval nodeValue3494 (mixedVector B) := by
    change mixedMoment B node3494 node3494Labels = _
    exact sound3494 B hB hF
  have h3502 : mixedVector B (Sum.inr 3502) = Sparse.eval nodeValue3502 (mixedVector B) := by
    change mixedMoment B node3502 node3502Labels = _
    exact sound3502 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm286, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2973, h3490, h3494, h3502, h3540, h4084, reducedSource240] using sourceEq286 B hB

theorem rowSound240 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row240 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck240, numericCheck240, reducedZero240 B hB hF, mul_zero]

theorem reducedZero241 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource241 (mixedVector B) = 0 := by
  have h2039 : mixedVector B (Sum.inr 2039) = Sparse.eval nodeValue2039 (mixedVector B) := by
    change mixedMoment B node2039 node2039Labels = _
    exact sound2039 B hB hF
  have h2592 : mixedVector B (Sum.inr 2592) = Sparse.eval nodeValue2592 (mixedVector B) := by
    change mixedMoment B node2592 node2592Labels = _
    exact sound2592 B hB hF
  have h3383 : mixedVector B (Sum.inr 3383) = Sparse.eval nodeValue3383 (mixedVector B) := by
    change mixedMoment B node3383 node3383Labels = _
    exact sound3383 B hB hF
  have h3490 : mixedVector B (Sum.inr 3490) = Sparse.eval nodeValue3490 (mixedVector B) := by
    change mixedMoment B node3490 node3490Labels = _
    exact sound3490 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm287, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2039, h2592, h3383, h3490, h3540, h3541, h4084, reducedSource241] using sourceEq287 B hB

theorem rowSound241 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row241 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck241, numericCheck241, reducedZero241 B hB hF, mul_zero]

theorem reducedZero242 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource242 (mixedVector B) = 0 := by
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3632 : mixedVector B (Sum.inr 3632) = Sparse.eval nodeValue3632 (mixedVector B) := by
    change mixedMoment B node3632 node3632Labels = _
    exact sound3632 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm288, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3533, h3539, h3540, h3541, h3544, h3632, h4084, reducedSource242] using sourceEq288 B hB

theorem rowSound242 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row242 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck242, numericCheck242, reducedZero242 B hB hF, mul_zero]

theorem reducedZero243 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource243 (mixedVector B) = 0 := by
  have h2054 : mixedVector B (Sum.inr 2054) = Sparse.eval nodeValue2054 (mixedVector B) := by
    change mixedMoment B node2054 node2054Labels = _
    exact sound2054 B hB hF
  have h3392 : mixedVector B (Sum.inr 3392) = Sparse.eval nodeValue3392 (mixedVector B) := by
    change mixedMoment B node3392 node3392Labels = _
    exact sound3392 B hB hF
  have h3494 : mixedVector B (Sum.inr 3494) = Sparse.eval nodeValue3494 (mixedVector B) := by
    change mixedMoment B node3494 node3494Labels = _
    exact sound3494 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm289, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2054, h3392, h3494, h3540, h3544, h3548, h4084, reducedSource243] using sourceEq289 B hB

theorem rowSound243 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row243 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck243, numericCheck243, reducedZero243 B hB hF, mul_zero]

theorem reducedZero244 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource244 (mixedVector B) = 0 := by
  have h1180 : mixedVector B (Sum.inr 1180) = Sparse.eval nodeValue1180 (mixedVector B) := by
    change mixedMoment B node1180 node1180Labels = _
    exact sound1180 B hB hF
  have h1181 : mixedVector B (Sum.inr 1181) = Sparse.eval nodeValue1181 (mixedVector B) := by
    change mixedMoment B node1181 node1181Labels = _
    exact sound1181 B hB hF
  have h1182 : mixedVector B (Sum.inr 1182) = Sparse.eval nodeValue1182 (mixedVector B) := by
    change mixedMoment B node1182 node1182Labels = _
    exact sound1182 B hB hF
  have h1189 : mixedVector B (Sum.inr 1189) = Sparse.eval nodeValue1189 (mixedVector B) := by
    change mixedMoment B node1189 node1189Labels = _
    exact sound1189 B hB hF
  have h1262 : mixedVector B (Sum.inr 1262) = Sparse.eval nodeValue1262 (mixedVector B) := by
    change mixedMoment B node1262 node1262Labels = _
    exact sound1262 B hB hF
  have h2454 : mixedVector B (Sum.inr 2454) = Sparse.eval nodeValue2454 (mixedVector B) := by
    change mixedMoment B node2454 node2454Labels = _
    exact sound2454 B hB hF
  have h2465 : mixedVector B (Sum.inr 2465) = Sparse.eval nodeValue2465 (mixedVector B) := by
    change mixedMoment B node2465 node2465Labels = _
    exact sound2465 B hB hF
  have h2495 : mixedVector B (Sum.inr 2495) = Sparse.eval nodeValue2495 (mixedVector B) := by
    change mixedMoment B node2495 node2495Labels = _
    exact sound2495 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2834 : mixedVector B (Sum.inr 2834) = Sparse.eval nodeValue2834 (mixedVector B) := by
    change mixedMoment B node2834 node2834Labels = _
    exact sound2834 B hB hF
  have h2835 : mixedVector B (Sum.inr 2835) = Sparse.eval nodeValue2835 (mixedVector B) := by
    change mixedMoment B node2835 node2835Labels = _
    exact sound2835 B hB hF
  have h2841 : mixedVector B (Sum.inr 2841) = Sparse.eval nodeValue2841 (mixedVector B) := by
    change mixedMoment B node2841 node2841Labels = _
    exact sound2841 B hB hF
  have h2905 : mixedVector B (Sum.inr 2905) = Sparse.eval nodeValue2905 (mixedVector B) := by
    change mixedMoment B node2905 node2905Labels = _
    exact sound2905 B hB hF
  have h2909 : mixedVector B (Sum.inr 2909) = Sparse.eval nodeValue2909 (mixedVector B) := by
    change mixedMoment B node2909 node2909Labels = _
    exact sound2909 B hB hF
  have h2934 : mixedVector B (Sum.inr 2934) = Sparse.eval nodeValue2934 (mixedVector B) := by
    change mixedMoment B node2934 node2934Labels = _
    exact sound2934 B hB hF
  have h2976 : mixedVector B (Sum.inr 2976) = Sparse.eval nodeValue2976 (mixedVector B) := by
    change mixedMoment B node2976 node2976Labels = _
    exact sound2976 B hB hF
  have h2979 : mixedVector B (Sum.inr 2979) = Sparse.eval nodeValue2979 (mixedVector B) := by
    change mixedMoment B node2979 node2979Labels = _
    exact sound2979 B hB hF
  have h2998 : mixedVector B (Sum.inr 2998) = Sparse.eval nodeValue2998 (mixedVector B) := by
    change mixedMoment B node2998 node2998Labels = _
    exact sound2998 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3109 : mixedVector B (Sum.inr 3109) = Sparse.eval nodeValue3109 (mixedVector B) := by
    change mixedMoment B node3109 node3109Labels = _
    exact sound3109 B hB hF
  have h3110 : mixedVector B (Sum.inr 3110) = Sparse.eval nodeValue3110 (mixedVector B) := by
    change mixedMoment B node3110 node3110Labels = _
    exact sound3110 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3883 : mixedVector B (Sum.inr 3883) = Sparse.eval nodeValue3883 (mixedVector B) := by
    change mixedMoment B node3883 node3883Labels = _
    exact sound3883 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  simpa only [sourceForm291, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1180, h1181, h1182, h1189, h1262, h2454, h2465, h2495, h2734, h2834, h2835, h2841, h2905, h2909, h2934, h2976, h2979, h2998, h3037, h3038, h3039, h3051, h3055, h3109, h3110, h3573, h3853, h3872, h3883, h3889, reducedSource244] using sourceEq291 B hB

theorem rowSound244 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row244 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck244, numericCheck244, reducedZero244 B hB hF, mul_zero]

theorem reducedZero245 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource245 (mixedVector B) = 0 := by
  have h2836 : mixedVector B (Sum.inr 2836) = Sparse.eval nodeValue2836 (mixedVector B) := by
    change mixedMoment B node2836 node2836Labels = _
    exact sound2836 B hB hF
  have h2837 : mixedVector B (Sum.inr 2837) = Sparse.eval nodeValue2837 (mixedVector B) := by
    change mixedMoment B node2837 node2837Labels = _
    exact sound2837 B hB hF
  have h2838 : mixedVector B (Sum.inr 2838) = Sparse.eval nodeValue2838 (mixedVector B) := by
    change mixedMoment B node2838 node2838Labels = _
    exact sound2838 B hB hF
  have h2841 : mixedVector B (Sum.inr 2841) = Sparse.eval nodeValue2841 (mixedVector B) := by
    change mixedMoment B node2841 node2841Labels = _
    exact sound2841 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3241 : mixedVector B (Sum.inr 3241) = Sparse.eval nodeValue3241 (mixedVector B) := by
    change mixedMoment B node3241 node3241Labels = _
    exact sound3241 B hB hF
  have h3242 : mixedVector B (Sum.inr 3242) = Sparse.eval nodeValue3242 (mixedVector B) := by
    change mixedMoment B node3242 node3242Labels = _
    exact sound3242 B hB hF
  have h3243 : mixedVector B (Sum.inr 3243) = Sparse.eval nodeValue3243 (mixedVector B) := by
    change mixedMoment B node3243 node3243Labels = _
    exact sound3243 B hB hF
  have h3246 : mixedVector B (Sum.inr 3246) = Sparse.eval nodeValue3246 (mixedVector B) := by
    change mixedMoment B node3246 node3246Labels = _
    exact sound3246 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3437 : mixedVector B (Sum.inr 3437) = Sparse.eval nodeValue3437 (mixedVector B) := by
    change mixedMoment B node3437 node3437Labels = _
    exact sound3437 B hB hF
  have h3461 : mixedVector B (Sum.inr 3461) = Sparse.eval nodeValue3461 (mixedVector B) := by
    change mixedMoment B node3461 node3461Labels = _
    exact sound3461 B hB hF
  have h3471 : mixedVector B (Sum.inr 3471) = Sparse.eval nodeValue3471 (mixedVector B) := by
    change mixedMoment B node3471 node3471Labels = _
    exact sound3471 B hB hF
  have h3472 : mixedVector B (Sum.inr 3472) = Sparse.eval nodeValue3472 (mixedVector B) := by
    change mixedMoment B node3472 node3472Labels = _
    exact sound3472 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h3515 : mixedVector B (Sum.inr 3515) = Sparse.eval nodeValue3515 (mixedVector B) := by
    change mixedMoment B node3515 node3515Labels = _
    exact sound3515 B hB hF
  have h3518 : mixedVector B (Sum.inr 3518) = Sparse.eval nodeValue3518 (mixedVector B) := by
    change mixedMoment B node3518 node3518Labels = _
    exact sound3518 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h3559 : mixedVector B (Sum.inr 3559) = Sparse.eval nodeValue3559 (mixedVector B) := by
    change mixedMoment B node3559 node3559Labels = _
    exact sound3559 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853 B hB hF
  have h3862 : mixedVector B (Sum.inr 3862) = Sparse.eval nodeValue3862 (mixedVector B) := by
    change mixedMoment B node3862 node3862Labels = _
    exact sound3862 B hB hF
  simpa only [sourceForm292, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2836, h2837, h2838, h2841, h3051, h3241, h3242, h3243, h3246, h3294, h3437, h3461, h3471, h3472, h3480, h3515, h3518, h3526, h3534, h3535, h3541, h3548, h3549, h3559, h3573, h3584, h3809, h3839, h3853, h3862, reducedSource245] using sourceEq292 B hB

theorem rowSound245 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row245 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck245, numericCheck245, reducedZero245 B hB hF, mul_zero]

theorem reducedZero246 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource246 (mixedVector B) = 0 := by
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3906 : mixedVector B (Sum.inr 3906) = Sparse.eval nodeValue3906 (mixedVector B) := by
    change mixedMoment B node3906 node3906Labels = _
    exact sound3906 B hB hF
  have h3907 : mixedVector B (Sum.inr 3907) = Sparse.eval nodeValue3907 (mixedVector B) := by
    change mixedMoment B node3907 node3907Labels = _
    exact sound3907 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm293, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2731, h2773, h3813, h3840, h3906, h3907, h4092, reducedSource246] using sourceEq293 B hB

theorem rowSound246 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row246 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck246, numericCheck246, reducedZero246 B hB hF, mul_zero]

theorem reducedZero247 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource247 (mixedVector B) = 0 := by
  have h1222 : mixedVector B (Sum.inr 1222) = Sparse.eval nodeValue1222 (mixedVector B) := by
    change mixedMoment B node1222 node1222Labels = _
    exact sound1222 B hB hF
  have h1224 : mixedVector B (Sum.inr 1224) = Sparse.eval nodeValue1224 (mixedVector B) := by
    change mixedMoment B node1224 node1224Labels = _
    exact sound1224 B hB hF
  have h1226 : mixedVector B (Sum.inr 1226) = Sparse.eval nodeValue1226 (mixedVector B) := by
    change mixedMoment B node1226 node1226Labels = _
    exact sound1226 B hB hF
  have h1237 : mixedVector B (Sum.inr 1237) = Sparse.eval nodeValue1237 (mixedVector B) := by
    change mixedMoment B node1237 node1237Labels = _
    exact sound1237 B hB hF
  have h1277 : mixedVector B (Sum.inr 1277) = Sparse.eval nodeValue1277 (mixedVector B) := by
    change mixedMoment B node1277 node1277Labels = _
    exact sound1277 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm294, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1222, h1224, h1226, h1237, h1277, h2731, h4092, reducedSource247] using sourceEq294 B hB

theorem rowSound247 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row247 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck247, numericCheck247, reducedZero247 B hB hF, mul_zero]

theorem reducedZero248 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource248 (mixedVector B) = 0 := by
  have h1277 : mixedVector B (Sum.inr 1277) = Sparse.eval nodeValue1277 (mixedVector B) := by
    change mixedMoment B node1277 node1277Labels = _
    exact sound1277 B hB hF
  have h2577 : mixedVector B (Sum.inr 2577) = Sparse.eval nodeValue2577 (mixedVector B) := by
    change mixedMoment B node2577 node2577Labels = _
    exact sound2577 B hB hF
  have h2650 : mixedVector B (Sum.inr 2650) = Sparse.eval nodeValue2650 (mixedVector B) := by
    change mixedMoment B node2650 node2650Labels = _
    exact sound2650 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm295, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1277, h2577, h2650, h2731, h2773, h2774, h4092, reducedSource248] using sourceEq295 B hB

theorem rowSound248 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row248 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck248, numericCheck248, reducedZero248 B hB hF, mul_zero]

theorem reducedZero249 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource249 (mixedVector B) = 0 := by
  have h2493 : mixedVector B (Sum.inr 2493) = Sparse.eval nodeValue2493 (mixedVector B) := by
    change mixedMoment B node2493 node2493Labels = _
    exact sound2493 B hB hF
  have h2495 : mixedVector B (Sum.inr 2495) = Sparse.eval nodeValue2495 (mixedVector B) := by
    change mixedMoment B node2495 node2495Labels = _
    exact sound2495 B hB hF
  have h2499 : mixedVector B (Sum.inr 2499) = Sparse.eval nodeValue2499 (mixedVector B) := by
    change mixedMoment B node2499 node2499Labels = _
    exact sound2499 B hB hF
  have h2512 : mixedVector B (Sum.inr 2512) = Sparse.eval nodeValue2512 (mixedVector B) := by
    change mixedMoment B node2512 node2512Labels = _
    exact sound2512 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm296, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2493, h2495, h2499, h2512, h2731, h3813, h4092, reducedSource249] using sourceEq296 B hB

theorem rowSound249 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row249 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck249, numericCheck249, reducedZero249 B hB hF, mul_zero]

theorem reducedZero250 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource250 (mixedVector B) = 0 := by
  have h1222 : mixedVector B (Sum.inr 1222) = Sparse.eval nodeValue1222 (mixedVector B) := by
    change mixedMoment B node1222 node1222Labels = _
    exact sound1222 B hB hF
  have h2493 : mixedVector B (Sum.inr 2493) = Sparse.eval nodeValue2493 (mixedVector B) := by
    change mixedMoment B node2493 node2493Labels = _
    exact sound2493 B hB hF
  have h2645 : mixedVector B (Sum.inr 2645) = Sparse.eval nodeValue2645 (mixedVector B) := by
    change mixedMoment B node2645 node2645Labels = _
    exact sound2645 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm297, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1222, h2493, h2645, h2730, h2731, h4092, reducedSource250] using sourceEq297 B hB

theorem rowSound250 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row250 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck250, numericCheck250, reducedZero250 B hB hF, mul_zero]

theorem reducedZero251 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource251 (mixedVector B) = 0 := by
  have h2547 : mixedVector B (Sum.inr 2547) = Sparse.eval nodeValue2547 (mixedVector B) := by
    change mixedMoment B node2547 node2547Labels = _
    exact sound2547 B hB hF
  have h2549 : mixedVector B (Sum.inr 2549) = Sparse.eval nodeValue2549 (mixedVector B) := by
    change mixedMoment B node2549 node2549Labels = _
    exact sound2549 B hB hF
  have h2554 : mixedVector B (Sum.inr 2554) = Sparse.eval nodeValue2554 (mixedVector B) := by
    change mixedMoment B node2554 node2554Labels = _
    exact sound2554 B hB hF
  have h2577 : mixedVector B (Sum.inr 2577) = Sparse.eval nodeValue2577 (mixedVector B) := by
    change mixedMoment B node2577 node2577Labels = _
    exact sound2577 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm298, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2547, h2549, h2554, h2577, h2731, h3840, h4092, reducedSource251] using sourceEq298 B hB

theorem rowSound251 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row251 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck251, numericCheck251, reducedZero251 B hB hF, mul_zero]

theorem reducedZero252 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource252 (mixedVector B) = 0 := by
  have h1237 : mixedVector B (Sum.inr 1237) = Sparse.eval nodeValue1237 (mixedVector B) := by
    change mixedMoment B node1237 node1237Labels = _
    exact sound1237 B hB hF
  have h2512 : mixedVector B (Sum.inr 2512) = Sparse.eval nodeValue2512 (mixedVector B) := by
    change mixedMoment B node2512 node2512Labels = _
    exact sound2512 B hB hF
  have h2554 : mixedVector B (Sum.inr 2554) = Sparse.eval nodeValue2554 (mixedVector B) := by
    change mixedMoment B node2554 node2554Labels = _
    exact sound2554 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm299, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1237, h2512, h2554, h2731, h2739, h2743, h4092, reducedSource252] using sourceEq299 B hB

theorem rowSound252 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row252 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck252, numericCheck252, reducedZero252 B hB hF, mul_zero]

theorem reducedZero253 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource253 (mixedVector B) = 0 := by
  have h2645 : mixedVector B (Sum.inr 2645) = Sparse.eval nodeValue2645 (mixedVector B) := by
    change mixedMoment B node2645 node2645Labels = _
    exact sound2645 B hB hF
  have h2647 : mixedVector B (Sum.inr 2647) = Sparse.eval nodeValue2647 (mixedVector B) := by
    change mixedMoment B node2647 node2647Labels = _
    exact sound2647 B hB hF
  have h2649 : mixedVector B (Sum.inr 2649) = Sparse.eval nodeValue2649 (mixedVector B) := by
    change mixedMoment B node2649 node2649Labels = _
    exact sound2649 B hB hF
  have h2650 : mixedVector B (Sum.inr 2650) = Sparse.eval nodeValue2650 (mixedVector B) := by
    change mixedMoment B node2650 node2650Labels = _
    exact sound2650 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm300, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2645, h2647, h2649, h2650, h2731, h2773, h4092, reducedSource253] using sourceEq300 B hB

theorem rowSound253 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row253 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck253, numericCheck253, reducedZero253 B hB hF, mul_zero]

theorem reducedZero254 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource254 (mixedVector B) = 0 := by
  have h1226 : mixedVector B (Sum.inr 1226) = Sparse.eval nodeValue1226 (mixedVector B) := by
    change mixedMoment B node1226 node1226Labels = _
    exact sound1226 B hB hF
  have h2499 : mixedVector B (Sum.inr 2499) = Sparse.eval nodeValue2499 (mixedVector B) := by
    change mixedMoment B node2499 node2499Labels = _
    exact sound2499 B hB hF
  have h2549 : mixedVector B (Sum.inr 2549) = Sparse.eval nodeValue2549 (mixedVector B) := by
    change mixedMoment B node2549 node2549Labels = _
    exact sound2549 B hB hF
  have h2649 : mixedVector B (Sum.inr 2649) = Sparse.eval nodeValue2649 (mixedVector B) := by
    change mixedMoment B node2649 node2649Labels = _
    exact sound2649 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm301, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1226, h2499, h2549, h2649, h2731, h2732, h4092, reducedSource254] using sourceEq301 B hB

theorem rowSound254 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row254 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck254, numericCheck254, reducedZero254 B hB hF, mul_zero]

theorem reducedZero255 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource255 (mixedVector B) = 0 := by
  have h988 : mixedVector B (Sum.inr 988) = Sparse.eval nodeValue988 (mixedVector B) := by
    change mixedMoment B node988 node988Labels = _
    exact sound988 B hB hF
  have h989 : mixedVector B (Sum.inr 989) = Sparse.eval nodeValue989 (mixedVector B) := by
    change mixedMoment B node989 node989Labels = _
    exact sound989 B hB hF
  have h993 : mixedVector B (Sum.inr 993) = Sparse.eval nodeValue993 (mixedVector B) := by
    change mixedMoment B node993 node993Labels = _
    exact sound993 B hB hF
  have h1001 : mixedVector B (Sum.inr 1001) = Sparse.eval nodeValue1001 (mixedVector B) := by
    change mixedMoment B node1001 node1001Labels = _
    exact sound1001 B hB hF
  have h1057 : mixedVector B (Sum.inr 1057) = Sparse.eval nodeValue1057 (mixedVector B) := by
    change mixedMoment B node1057 node1057Labels = _
    exact sound1057 B hB hF
  have h2390 : mixedVector B (Sum.inr 2390) = Sparse.eval nodeValue2390 (mixedVector B) := by
    change mixedMoment B node2390 node2390Labels = _
    exact sound2390 B hB hF
  have h2391 : mixedVector B (Sum.inr 2391) = Sparse.eval nodeValue2391 (mixedVector B) := by
    change mixedMoment B node2391 node2391Labels = _
    exact sound2391 B hB hF
  have h2395 : mixedVector B (Sum.inr 2395) = Sparse.eval nodeValue2395 (mixedVector B) := by
    change mixedMoment B node2395 node2395Labels = _
    exact sound2395 B hB hF
  have h2401 : mixedVector B (Sum.inr 2401) = Sparse.eval nodeValue2401 (mixedVector B) := by
    change mixedMoment B node2401 node2401Labels = _
    exact sound2401 B hB hF
  have h2453 : mixedVector B (Sum.inr 2453) = Sparse.eval nodeValue2453 (mixedVector B) := by
    change mixedMoment B node2453 node2453Labels = _
    exact sound2453 B hB hF
  have h2456 : mixedVector B (Sum.inr 2456) = Sparse.eval nodeValue2456 (mixedVector B) := by
    change mixedMoment B node2456 node2456Labels = _
    exact sound2456 B hB hF
  have h2460 : mixedVector B (Sum.inr 2460) = Sparse.eval nodeValue2460 (mixedVector B) := by
    change mixedMoment B node2460 node2460Labels = _
    exact sound2460 B hB hF
  have h2493 : mixedVector B (Sum.inr 2493) = Sparse.eval nodeValue2493 (mixedVector B) := by
    change mixedMoment B node2493 node2493Labels = _
    exact sound2493 B hB hF
  have h2569 : mixedVector B (Sum.inr 2569) = Sparse.eval nodeValue2569 (mixedVector B) := by
    change mixedMoment B node2569 node2569Labels = _
    exact sound2569 B hB hF
  have h2615 : mixedVector B (Sum.inr 2615) = Sparse.eval nodeValue2615 (mixedVector B) := by
    change mixedMoment B node2615 node2615Labels = _
    exact sound2615 B hB hF
  have h2621 : mixedVector B (Sum.inr 2621) = Sparse.eval nodeValue2621 (mixedVector B) := by
    change mixedMoment B node2621 node2621Labels = _
    exact sound2621 B hB hF
  have h2637 : mixedVector B (Sum.inr 2637) = Sparse.eval nodeValue2637 (mixedVector B) := by
    change mixedMoment B node2637 node2637Labels = _
    exact sound2637 B hB hF
  have h2664 : mixedVector B (Sum.inr 2664) = Sparse.eval nodeValue2664 (mixedVector B) := by
    change mixedMoment B node2664 node2664Labels = _
    exact sound2664 B hB hF
  have h2698 : mixedVector B (Sum.inr 2698) = Sparse.eval nodeValue2698 (mixedVector B) := by
    change mixedMoment B node2698 node2698Labels = _
    exact sound2698 B hB hF
  have h2706 : mixedVector B (Sum.inr 2706) = Sparse.eval nodeValue2706 (mixedVector B) := by
    change mixedMoment B node2706 node2706Labels = _
    exact sound2706 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h2775 : mixedVector B (Sum.inr 2775) = Sparse.eval nodeValue2775 (mixedVector B) := by
    change mixedMoment B node2775 node2775Labels = _
    exact sound2775 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h3885 : mixedVector B (Sum.inr 3885) = Sparse.eval nodeValue3885 (mixedVector B) := by
    change mixedMoment B node3885 node3885Labels = _
    exact sound3885 B hB hF
  have h3887 : mixedVector B (Sum.inr 3887) = Sparse.eval nodeValue3887 (mixedVector B) := by
    change mixedMoment B node3887 node3887Labels = _
    exact sound3887 B hB hF
  have h3995 : mixedVector B (Sum.inr 3995) = Sparse.eval nodeValue3995 (mixedVector B) := by
    change mixedMoment B node3995 node3995Labels = _
    exact sound3995 B hB hF
  simpa only [sourceForm303, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h988, h989, h993, h1001, h1057, h2390, h2391, h2395, h2401, h2453, h2456, h2460, h2493, h2569, h2615, h2621, h2637, h2664, h2698, h2706, h2730, h2731, h2738, h2775, h3880, h3884, h3885, h3887, h3995, reducedSource255] using sourceEq303 B hB

theorem rowSound255 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row255 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck255, numericCheck255, reducedZero255 B hB hF, mul_zero]

theorem sourceRowsAt240 : MixedData.sourceRows (240 : Fin 2425) =
    MixedData.row240 := by decide +kernel

theorem sourceRowsAt241 : MixedData.sourceRows (241 : Fin 2425) =
    MixedData.row241 := by decide +kernel

theorem sourceRowsAt242 : MixedData.sourceRows (242 : Fin 2425) =
    MixedData.row242 := by decide +kernel

theorem sourceRowsAt243 : MixedData.sourceRows (243 : Fin 2425) =
    MixedData.row243 := by decide +kernel

theorem sourceRowsAt244 : MixedData.sourceRows (244 : Fin 2425) =
    MixedData.row244 := by decide +kernel

theorem sourceRowsAt245 : MixedData.sourceRows (245 : Fin 2425) =
    MixedData.row245 := by decide +kernel

theorem sourceRowsAt246 : MixedData.sourceRows (246 : Fin 2425) =
    MixedData.row246 := by decide +kernel

theorem sourceRowsAt247 : MixedData.sourceRows (247 : Fin 2425) =
    MixedData.row247 := by decide +kernel

theorem sourceRowsAt248 : MixedData.sourceRows (248 : Fin 2425) =
    MixedData.row248 := by decide +kernel

theorem sourceRowsAt249 : MixedData.sourceRows (249 : Fin 2425) =
    MixedData.row249 := by decide +kernel

theorem sourceRowsAt250 : MixedData.sourceRows (250 : Fin 2425) =
    MixedData.row250 := by decide +kernel

theorem sourceRowsAt251 : MixedData.sourceRows (251 : Fin 2425) =
    MixedData.row251 := by decide +kernel

theorem sourceRowsAt252 : MixedData.sourceRows (252 : Fin 2425) =
    MixedData.row252 := by decide +kernel

theorem sourceRowsAt253 : MixedData.sourceRows (253 : Fin 2425) =
    MixedData.row253 := by decide +kernel

theorem sourceRowsAt254 : MixedData.sourceRows (254 : Fin 2425) =
    MixedData.row254 := by decide +kernel

theorem sourceRowsAt255 : MixedData.sourceRows (255 : Fin 2425) =
    MixedData.row255 := by decide +kernel

theorem chunkSound15 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 15) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 240 ∨ k.val = 241 ∨ k.val = 242 ∨ k.val = 243 ∨ k.val = 244 ∨ k.val = 245 ∨ k.val = 246 ∨ k.val = 247 ∨ k.val = 248 ∨ k.val = 249 ∨ k.val = 250 ∨ k.val = 251 ∨ k.val = 252 ∨ k.val = 253 ∨ k.val = 254 ∨ k.val = 255 := by omega
  rcases heq with h240 | h241 | h242 | h243 | h244 | h245 | h246 | h247 | h248 | h249 | h250 | h251 | h252 | h253 | h254 | h255
  · have he : k = (240 : Fin 2425) := Fin.ext h240
    subst k
    rw [sourceRowsAt240]
    exact rowSound240 B hB hF
  · have he : k = (241 : Fin 2425) := Fin.ext h241
    subst k
    rw [sourceRowsAt241]
    exact rowSound241 B hB hF
  · have he : k = (242 : Fin 2425) := Fin.ext h242
    subst k
    rw [sourceRowsAt242]
    exact rowSound242 B hB hF
  · have he : k = (243 : Fin 2425) := Fin.ext h243
    subst k
    rw [sourceRowsAt243]
    exact rowSound243 B hB hF
  · have he : k = (244 : Fin 2425) := Fin.ext h244
    subst k
    rw [sourceRowsAt244]
    exact rowSound244 B hB hF
  · have he : k = (245 : Fin 2425) := Fin.ext h245
    subst k
    rw [sourceRowsAt245]
    exact rowSound245 B hB hF
  · have he : k = (246 : Fin 2425) := Fin.ext h246
    subst k
    rw [sourceRowsAt246]
    exact rowSound246 B hB hF
  · have he : k = (247 : Fin 2425) := Fin.ext h247
    subst k
    rw [sourceRowsAt247]
    exact rowSound247 B hB hF
  · have he : k = (248 : Fin 2425) := Fin.ext h248
    subst k
    rw [sourceRowsAt248]
    exact rowSound248 B hB hF
  · have he : k = (249 : Fin 2425) := Fin.ext h249
    subst k
    rw [sourceRowsAt249]
    exact rowSound249 B hB hF
  · have he : k = (250 : Fin 2425) := Fin.ext h250
    subst k
    rw [sourceRowsAt250]
    exact rowSound250 B hB hF
  · have he : k = (251 : Fin 2425) := Fin.ext h251
    subst k
    rw [sourceRowsAt251]
    exact rowSound251 B hB hF
  · have he : k = (252 : Fin 2425) := Fin.ext h252
    subst k
    rw [sourceRowsAt252]
    exact rowSound252 B hB hF
  · have he : k = (253 : Fin 2425) := Fin.ext h253
    subst k
    rw [sourceRowsAt253]
    exact rowSound253 B hB hF
  · have he : k = (254 : Fin 2425) := Fin.ext h254
    subst k
    rw [sourceRowsAt254]
    exact rowSound254 B hB hF
  · have he : k = (255 : Fin 2425) := Fin.ext h255
    subst k
    rw [sourceRowsAt255]
    exact rowSound255 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
