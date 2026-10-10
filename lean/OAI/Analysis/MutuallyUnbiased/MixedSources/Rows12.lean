import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources7

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero192 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource192 (mixedVector B) = 0 := by
  have h2513 : mixedVector B (Sum.inr 2513) = Sparse.eval nodeValue2513 (mixedVector B) := by
    change mixedMoment B node2513 node2513Labels = _
    exact sound2513 B hB hF
  have h2520 : mixedVector B (Sum.inr 2520) = Sparse.eval nodeValue2520 (mixedVector B) := by
    change mixedMoment B node2520 node2520Labels = _
    exact sound2520 B hB hF
  have h2522 : mixedVector B (Sum.inr 2522) = Sparse.eval nodeValue2522 (mixedVector B) := by
    change mixedMoment B node2522 node2522Labels = _
    exact sound2522 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm226, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2513, h2520, h2522, h2744, h3626, h4084, reducedSource192] using sourceEq226 B hB

theorem rowSound192 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row192 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck192, numericCheck192, reducedZero192 B hB hF, mul_zero]

theorem reducedZero193 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource193 (mixedVector B) = 0 := by
  have h1238 : mixedVector B (Sum.inr 1238) = Sparse.eval nodeValue1238 (mixedVector B) := by
    change mixedMoment B node1238 node1238Labels = _
    exact sound1238 B hB hF
  have h2133 : mixedVector B (Sum.inr 2133) = Sparse.eval nodeValue2133 (mixedVector B) := by
    change mixedMoment B node2133 node2133Labels = _
    exact sound2133 B hB hF
  have h2513 : mixedVector B (Sum.inr 2513) = Sparse.eval nodeValue2513 (mixedVector B) := by
    change mixedMoment B node2513 node2513Labels = _
    exact sound2513 B hB hF
  have h2555 : mixedVector B (Sum.inr 2555) = Sparse.eval nodeValue2555 (mixedVector B) := by
    change mixedMoment B node2555 node2555Labels = _
    exact sound2555 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm227, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1238, h2133, h2513, h2555, h2738, h2744, h4084, reducedSource193] using sourceEq227 B hB

theorem rowSound193 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row193 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck193, numericCheck193, reducedZero193 B hB hF, mul_zero]

theorem reducedZero194 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource194 (mixedVector B) = 0 := by
  have h2555 : mixedVector B (Sum.inr 2555) = Sparse.eval nodeValue2555 (mixedVector B) := by
    change mixedMoment B node2555 node2555Labels = _
    exact sound2555 B hB hF
  have h2559 : mixedVector B (Sum.inr 2559) = Sparse.eval nodeValue2559 (mixedVector B) := by
    change mixedMoment B node2559 node2559Labels = _
    exact sound2559 B hB hF
  have h2560 : mixedVector B (Sum.inr 2560) = Sparse.eval nodeValue2560 (mixedVector B) := by
    change mixedMoment B node2560 node2560Labels = _
    exact sound2560 B hB hF
  have h2592 : mixedVector B (Sum.inr 2592) = Sparse.eval nodeValue2592 (mixedVector B) := by
    change mixedMoment B node2592 node2592Labels = _
    exact sound2592 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm228, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2555, h2559, h2560, h2592, h2744, h3541, h4084, reducedSource194] using sourceEq228 B hB

theorem rowSound194 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row194 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck194, numericCheck194, reducedZero194 B hB hF, mul_zero]

theorem reducedZero195 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource195 (mixedVector B) = 0 := by
  have h1245 : mixedVector B (Sum.inr 1245) = Sparse.eval nodeValue1245 (mixedVector B) := by
    change mixedMoment B node1245 node1245Labels = _
    exact sound1245 B hB hF
  have h2522 : mixedVector B (Sum.inr 2522) = Sparse.eval nodeValue2522 (mixedVector B) := by
    change mixedMoment B node2522 node2522Labels = _
    exact sound2522 B hB hF
  have h2560 : mixedVector B (Sum.inr 2560) = Sparse.eval nodeValue2560 (mixedVector B) := by
    change mixedMoment B node2560 node2560Labels = _
    exact sound2560 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm229, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1245, h2522, h2560, h2740, h2744, h4084, reducedSource195] using sourceEq229 B hB

theorem rowSound195 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row195 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck195, numericCheck195, reducedZero195 B hB hF, mul_zero]

theorem reducedZero196 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource196 (mixedVector B) = 0 := by
  have h2133 : mixedVector B (Sum.inr 2133) = Sparse.eval nodeValue2133 (mixedVector B) := by
    change mixedMoment B node2133 node2133Labels = _
    exact sound2133 B hB hF
  have h2136 : mixedVector B (Sum.inr 2136) = Sparse.eval nodeValue2136 (mixedVector B) := by
    change mixedMoment B node2136 node2136Labels = _
    exact sound2136 B hB hF
  have h2138 : mixedVector B (Sum.inr 2138) = Sparse.eval nodeValue2138 (mixedVector B) := by
    change mixedMoment B node2138 node2138Labels = _
    exact sound2138 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm230, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2133, h2136, h2138, h2279, h2744, h4084, reducedSource196] using sourceEq230 B hB

theorem rowSound196 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row196 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck196, numericCheck196, reducedZero196 B hB hF, mul_zero]

theorem reducedZero197 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource197 (mixedVector B) = 0 := by
  have h1244 : mixedVector B (Sum.inr 1244) = Sparse.eval nodeValue1244 (mixedVector B) := by
    change mixedMoment B node1244 node1244Labels = _
    exact sound1244 B hB hF
  have h2136 : mixedVector B (Sum.inr 2136) = Sparse.eval nodeValue2136 (mixedVector B) := by
    change mixedMoment B node2136 node2136Labels = _
    exact sound2136 B hB hF
  have h2520 : mixedVector B (Sum.inr 2520) = Sparse.eval nodeValue2520 (mixedVector B) := by
    change mixedMoment B node2520 node2520Labels = _
    exact sound2520 B hB hF
  have h2559 : mixedVector B (Sum.inr 2559) = Sparse.eval nodeValue2559 (mixedVector B) := by
    change mixedMoment B node2559 node2559Labels = _
    exact sound2559 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm231, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1244, h2136, h2520, h2559, h2744, h4084, reducedSource197] using sourceEq231 B hB

theorem rowSound197 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row197 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck197, numericCheck197, reducedZero197 B hB hF, mul_zero]

theorem reducedZero198 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource198 (mixedVector B) = 0 := by
  have h1006 : mixedVector B (Sum.inr 1006) = Sparse.eval nodeValue1006 (mixedVector B) := by
    change mixedMoment B node1006 node1006Labels = _
    exact sound1006 B hB hF
  have h1010 : mixedVector B (Sum.inr 1010) = Sparse.eval nodeValue1010 (mixedVector B) := by
    change mixedMoment B node1010 node1010Labels = _
    exact sound1010 B hB hF
  have h1011 : mixedVector B (Sum.inr 1011) = Sparse.eval nodeValue1011 (mixedVector B) := by
    change mixedMoment B node1011 node1011Labels = _
    exact sound1011 B hB hF
  have h1084 : mixedVector B (Sum.inr 1084) = Sparse.eval nodeValue1084 (mixedVector B) := by
    change mixedMoment B node1084 node1084Labels = _
    exact sound1084 B hB hF
  have h2405 : mixedVector B (Sum.inr 2405) = Sparse.eval nodeValue2405 (mixedVector B) := by
    change mixedMoment B node2405 node2405Labels = _
    exact sound2405 B hB hF
  have h2408 : mixedVector B (Sum.inr 2408) = Sparse.eval nodeValue2408 (mixedVector B) := by
    change mixedMoment B node2408 node2408Labels = _
    exact sound2408 B hB hF
  have h2409 : mixedVector B (Sum.inr 2409) = Sparse.eval nodeValue2409 (mixedVector B) := by
    change mixedMoment B node2409 node2409Labels = _
    exact sound2409 B hB hF
  have h2463 : mixedVector B (Sum.inr 2463) = Sparse.eval nodeValue2463 (mixedVector B) := by
    change mixedMoment B node2463 node2463Labels = _
    exact sound2463 B hB hF
  have h2465 : mixedVector B (Sum.inr 2465) = Sparse.eval nodeValue2465 (mixedVector B) := by
    change mixedMoment B node2465 node2465Labels = _
    exact sound2465 B hB hF
  have h2466 : mixedVector B (Sum.inr 2466) = Sparse.eval nodeValue2466 (mixedVector B) := by
    change mixedMoment B node2466 node2466Labels = _
    exact sound2466 B hB hF
  have h2513 : mixedVector B (Sum.inr 2513) = Sparse.eval nodeValue2513 (mixedVector B) := by
    change mixedMoment B node2513 node2513Labels = _
    exact sound2513 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h2776 : mixedVector B (Sum.inr 2776) = Sparse.eval nodeValue2776 (mixedVector B) := by
    change mixedMoment B node2776 node2776Labels = _
    exact sound2776 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  simpa only [sourceForm233, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1006, h1010, h1011, h1084, h2405, h2408, h2409, h2463, h2465, h2466, h2513, h2732, h2734, h2735, h2737, h2776, h2781, h3573, h3583, h3584, h3889, reducedSource198] using sourceEq233 B hB

theorem rowSound198 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row198 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck198, numericCheck198, reducedZero198 B hB hF, mul_zero]

theorem reducedZero199 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource199 (mixedVector B) = 0 := by
  have h1184 : mixedVector B (Sum.inr 1184) = Sparse.eval nodeValue1184 (mixedVector B) := by
    change mixedMoment B node1184 node1184Labels = _
    exact sound1184 B hB hF
  have h1186 : mixedVector B (Sum.inr 1186) = Sparse.eval nodeValue1186 (mixedVector B) := by
    change mixedMoment B node1186 node1186Labels = _
    exact sound1186 B hB hF
  have h1192 : mixedVector B (Sum.inr 1192) = Sparse.eval nodeValue1192 (mixedVector B) := by
    change mixedMoment B node1192 node1192Labels = _
    exact sound1192 B hB hF
  have h1292 : mixedVector B (Sum.inr 1292) = Sparse.eval nodeValue1292 (mixedVector B) := by
    change mixedMoment B node1292 node1292Labels = _
    exact sound1292 B hB hF
  have h1610 : mixedVector B (Sum.inr 1610) = Sparse.eval nodeValue1610 (mixedVector B) := by
    change mixedMoment B node1610 node1610Labels = _
    exact sound1610 B hB hF
  have h1628 : mixedVector B (Sum.inr 1628) = Sparse.eval nodeValue1628 (mixedVector B) := by
    change mixedMoment B node1628 node1628Labels = _
    exact sound1628 B hB hF
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h2837 : mixedVector B (Sum.inr 2837) = Sparse.eval nodeValue2837 (mixedVector B) := by
    change mixedMoment B node2837 node2837Labels = _
    exact sound2837 B hB hF
  have h2842 : mixedVector B (Sum.inr 2842) = Sparse.eval nodeValue2842 (mixedVector B) := by
    change mixedMoment B node2842 node2842Labels = _
    exact sound2842 B hB hF
  have h2906 : mixedVector B (Sum.inr 2906) = Sparse.eval nodeValue2906 (mixedVector B) := by
    change mixedMoment B node2906 node2906Labels = _
    exact sound2906 B hB hF
  have h2910 : mixedVector B (Sum.inr 2910) = Sparse.eval nodeValue2910 (mixedVector B) := by
    change mixedMoment B node2910 node2910Labels = _
    exact sound2910 B hB hF
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h3024 : mixedVector B (Sum.inr 3024) = Sparse.eval nodeValue3024 (mixedVector B) := by
    change mixedMoment B node3024 node3024Labels = _
    exact sound3024 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3119 : mixedVector B (Sum.inr 3119) = Sparse.eval nodeValue3119 (mixedVector B) := by
    change mixedMoment B node3119 node3119Labels = _
    exact sound3119 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3862 : mixedVector B (Sum.inr 3862) = Sparse.eval nodeValue3862 (mixedVector B) := by
    change mixedMoment B node3862 node3862Labels = _
    exact sound3862 B hB hF
  simpa only [sourceForm234, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1184, h1186, h1192, h1292, h1610, h1628, h1716, h2837, h2842, h2906, h2910, h2952, h3024, h3051, h3055, h3098, h3119, h3541, h3549, h3626, h3862, reducedSource199] using sourceEq234 B hB

theorem rowSound199 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row199 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck199, numericCheck199, reducedZero199 B hB hF, mul_zero]

theorem reducedZero200 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource200 (mixedVector B) = 0 := by
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  have h3907 : mixedVector B (Sum.inr 3907) = Sparse.eval nodeValue3907 (mixedVector B) := by
    change mixedMoment B node3907 node3907Labels = _
    exact sound3907 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm235, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2773, h2774, h2777, h2782, h3907, h4092, reducedSource200] using sourceEq235 B hB

theorem rowSound200 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row200 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck200, numericCheck200, reducedZero200 B hB hF, mul_zero]

theorem reducedZero201 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource201 (mixedVector B) = 0 := by
  have h1282 : mixedVector B (Sum.inr 1282) = Sparse.eval nodeValue1282 (mixedVector B) := by
    change mixedMoment B node1282 node1282Labels = _
    exact sound1282 B hB hF
  have h1422 : mixedVector B (Sum.inr 1422) = Sparse.eval nodeValue1422 (mixedVector B) := by
    change mixedMoment B node1422 node1422Labels = _
    exact sound1422 B hB hF
  have h1424 : mixedVector B (Sum.inr 1424) = Sparse.eval nodeValue1424 (mixedVector B) := by
    change mixedMoment B node1424 node1424Labels = _
    exact sound1424 B hB hF
  have h1436 : mixedVector B (Sum.inr 1436) = Sparse.eval nodeValue1436 (mixedVector B) := by
    change mixedMoment B node1436 node1436Labels = _
    exact sound1436 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm236, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1282, h1422, h1424, h1436, h2777, h4092, reducedSource201] using sourceEq236 B hB

theorem rowSound201 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row201 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck201, numericCheck201, reducedZero201 B hB hF, mul_zero]

theorem reducedZero202 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource202 (mixedVector B) = 0 := by
  have h1436 : mixedVector B (Sum.inr 1436) = Sparse.eval nodeValue1436 (mixedVector B) := by
    change mixedMoment B node1436 node1436Labels = _
    exact sound1436 B hB hF
  have h2759 : mixedVector B (Sum.inr 2759) = Sparse.eval nodeValue2759 (mixedVector B) := by
    change mixedMoment B node2759 node2759Labels = _
    exact sound2759 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm237, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1436, h2759, h2769, h2777, h3054, h4092, reducedSource202] using sourceEq237 B hB

theorem rowSound202 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row202 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck202, numericCheck202, reducedZero202 B hB hF, mul_zero]

theorem reducedZero203 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource203 (mixedVector B) = 0 := by
  have h1283 : mixedVector B (Sum.inr 1283) = Sparse.eval nodeValue1283 (mixedVector B) := by
    change mixedMoment B node1283 node1283Labels = _
    exact sound1283 B hB hF
  have h2582 : mixedVector B (Sum.inr 2582) = Sparse.eval nodeValue2582 (mixedVector B) := by
    change mixedMoment B node2582 node2582Labels = _
    exact sound2582 B hB hF
  have h2651 : mixedVector B (Sum.inr 2651) = Sparse.eval nodeValue2651 (mixedVector B) := by
    change mixedMoment B node2651 node2651Labels = _
    exact sound2651 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm238, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1283, h2582, h2651, h2774, h2777, h4092, reducedSource203] using sourceEq238 B hB

theorem rowSound203 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row203 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck203, numericCheck203, reducedZero203 B hB hF, mul_zero]

theorem reducedZero204 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource204 (mixedVector B) = 0 := by
  have h1422 : mixedVector B (Sum.inr 1422) = Sparse.eval nodeValue1422 (mixedVector B) := by
    change mixedMoment B node1422 node1422Labels = _
    exact sound1422 B hB hF
  have h2580 : mixedVector B (Sum.inr 2580) = Sparse.eval nodeValue2580 (mixedVector B) := by
    change mixedMoment B node2580 node2580Labels = _
    exact sound2580 B hB hF
  have h2582 : mixedVector B (Sum.inr 2582) = Sparse.eval nodeValue2582 (mixedVector B) := by
    change mixedMoment B node2582 node2582Labels = _
    exact sound2582 B hB hF
  have h2600 : mixedVector B (Sum.inr 2600) = Sparse.eval nodeValue2600 (mixedVector B) := by
    change mixedMoment B node2600 node2600Labels = _
    exact sound2600 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm239, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1422, h2580, h2582, h2600, h2777, h3038, h4092, reducedSource204] using sourceEq239 B hB

theorem rowSound204 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row204 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck204, numericCheck204, reducedZero204 B hB hF, mul_zero]

theorem reducedZero205 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource205 (mixedVector B) = 0 := by
  have h1280 : mixedVector B (Sum.inr 1280) = Sparse.eval nodeValue1280 (mixedVector B) := by
    change mixedMoment B node1280 node1280Labels = _
    exact sound1280 B hB hF
  have h2580 : mixedVector B (Sum.inr 2580) = Sparse.eval nodeValue2580 (mixedVector B) := by
    change mixedMoment B node2580 node2580Labels = _
    exact sound2580 B hB hF
  have h2647 : mixedVector B (Sum.inr 2647) = Sparse.eval nodeValue2647 (mixedVector B) := by
    change mixedMoment B node2647 node2647Labels = _
    exact sound2647 B hB hF
  have h2759 : mixedVector B (Sum.inr 2759) = Sparse.eval nodeValue2759 (mixedVector B) := by
    change mixedMoment B node2759 node2759Labels = _
    exact sound2759 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm240, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1280, h2580, h2647, h2759, h2773, h2777, h4092, reducedSource205] using sourceEq240 B hB

theorem rowSound205 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row205 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck205, numericCheck205, reducedZero205 B hB hF, mul_zero]

theorem reducedZero206 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource206 (mixedVector B) = 0 := by
  have h1280 : mixedVector B (Sum.inr 1280) = Sparse.eval nodeValue1280 (mixedVector B) := by
    change mixedMoment B node1280 node1280Labels = _
    exact sound1280 B hB hF
  have h1282 : mixedVector B (Sum.inr 1282) = Sparse.eval nodeValue1282 (mixedVector B) := by
    change mixedMoment B node1282 node1282Labels = _
    exact sound1282 B hB hF
  have h1283 : mixedVector B (Sum.inr 1283) = Sparse.eval nodeValue1283 (mixedVector B) := by
    change mixedMoment B node1283 node1283Labels = _
    exact sound1283 B hB hF
  have h1306 : mixedVector B (Sum.inr 1306) = Sparse.eval nodeValue1306 (mixedVector B) := by
    change mixedMoment B node1306 node1306Labels = _
    exact sound1306 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm241, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1280, h1282, h1283, h1306, h2777, h4092, reducedSource206] using sourceEq241 B hB

theorem rowSound206 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row206 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck206, numericCheck206, reducedZero206 B hB hF, mul_zero]

theorem reducedZero207 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource207 (mixedVector B) = 0 := by
  have h1060 : mixedVector B (Sum.inr 1060) = Sparse.eval nodeValue1060 (mixedVector B) := by
    change mixedMoment B node1060 node1060Labels = _
    exact sound1060 B hB hF
  have h1061 : mixedVector B (Sum.inr 1061) = Sparse.eval nodeValue1061 (mixedVector B) := by
    change mixedMoment B node1061 node1061Labels = _
    exact sound1061 B hB hF
  have h1062 : mixedVector B (Sum.inr 1062) = Sparse.eval nodeValue1062 (mixedVector B) := by
    change mixedMoment B node1062 node1062Labels = _
    exact sound1062 B hB hF
  have h1088 : mixedVector B (Sum.inr 1088) = Sparse.eval nodeValue1088 (mixedVector B) := by
    change mixedMoment B node1088 node1088Labels = _
    exact sound1088 B hB hF
  have h2496 : mixedVector B (Sum.inr 2496) = Sparse.eval nodeValue2496 (mixedVector B) := by
    change mixedMoment B node2496 node2496Labels = _
    exact sound2496 B hB hF
  have h2497 : mixedVector B (Sum.inr 2497) = Sparse.eval nodeValue2497 (mixedVector B) := by
    change mixedMoment B node2497 node2497Labels = _
    exact sound2497 B hB hF
  have h2498 : mixedVector B (Sum.inr 2498) = Sparse.eval nodeValue2498 (mixedVector B) := by
    change mixedMoment B node2498 node2498Labels = _
    exact sound2498 B hB hF
  have h2516 : mixedVector B (Sum.inr 2516) = Sparse.eval nodeValue2516 (mixedVector B) := by
    change mixedMoment B node2516 node2516Labels = _
    exact sound2516 B hB hF
  have h2641 : mixedVector B (Sum.inr 2641) = Sparse.eval nodeValue2641 (mixedVector B) := by
    change mixedMoment B node2641 node2641Labels = _
    exact sound2641 B hB hF
  have h2642 : mixedVector B (Sum.inr 2642) = Sparse.eval nodeValue2642 (mixedVector B) := by
    change mixedMoment B node2642 node2642Labels = _
    exact sound2642 B hB hF
  have h2643 : mixedVector B (Sum.inr 2643) = Sparse.eval nodeValue2643 (mixedVector B) := by
    change mixedMoment B node2643 node2643Labels = _
    exact sound2643 B hB hF
  have h2748 : mixedVector B (Sum.inr 2748) = Sparse.eval nodeValue2748 (mixedVector B) := by
    change mixedMoment B node2748 node2748Labels = _
    exact sound2748 B hB hF
  have h2761 : mixedVector B (Sum.inr 2761) = Sparse.eval nodeValue2761 (mixedVector B) := by
    change mixedMoment B node2761 node2761Labels = _
    exact sound2761 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2771 : mixedVector B (Sum.inr 2771) = Sparse.eval nodeValue2771 (mixedVector B) := by
    change mixedMoment B node2771 node2771Labels = _
    exact sound2771 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h2778 : mixedVector B (Sum.inr 2778) = Sparse.eval nodeValue2778 (mixedVector B) := by
    change mixedMoment B node2778 node2778Labels = _
    exact sound2778 B hB hF
  have h2789 : mixedVector B (Sum.inr 2789) = Sparse.eval nodeValue2789 (mixedVector B) := by
    change mixedMoment B node2789 node2789Labels = _
    exact sound2789 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3110 : mixedVector B (Sum.inr 3110) = Sparse.eval nodeValue3110 (mixedVector B) := by
    change mixedMoment B node3110 node3110Labels = _
    exact sound3110 B hB hF
  have h3121 : mixedVector B (Sum.inr 3121) = Sparse.eval nodeValue3121 (mixedVector B) := by
    change mixedMoment B node3121 node3121Labels = _
    exact sound3121 B hB hF
  simpa only [sourceForm244, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1060, h1061, h1062, h1088, h2496, h2497, h2498, h2516, h2641, h2642, h2643, h2748, h2761, h2765, h2771, h2777, h2778, h2789, h3086, h3110, h3121, reducedSource207] using sourceEq244 B hB

theorem rowSound207 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row207 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck207, numericCheck207, reducedZero207 B hB hF, mul_zero]

theorem sourceRowsAt192 : MixedData.sourceRows (192 : Fin 2425) =
    MixedData.row192 := by decide +kernel

theorem sourceRowsAt193 : MixedData.sourceRows (193 : Fin 2425) =
    MixedData.row193 := by decide +kernel

theorem sourceRowsAt194 : MixedData.sourceRows (194 : Fin 2425) =
    MixedData.row194 := by decide +kernel

theorem sourceRowsAt195 : MixedData.sourceRows (195 : Fin 2425) =
    MixedData.row195 := by decide +kernel

theorem sourceRowsAt196 : MixedData.sourceRows (196 : Fin 2425) =
    MixedData.row196 := by decide +kernel

theorem sourceRowsAt197 : MixedData.sourceRows (197 : Fin 2425) =
    MixedData.row197 := by decide +kernel

theorem sourceRowsAt198 : MixedData.sourceRows (198 : Fin 2425) =
    MixedData.row198 := by decide +kernel

theorem sourceRowsAt199 : MixedData.sourceRows (199 : Fin 2425) =
    MixedData.row199 := by decide +kernel

theorem sourceRowsAt200 : MixedData.sourceRows (200 : Fin 2425) =
    MixedData.row200 := by decide +kernel

theorem sourceRowsAt201 : MixedData.sourceRows (201 : Fin 2425) =
    MixedData.row201 := by decide +kernel

theorem sourceRowsAt202 : MixedData.sourceRows (202 : Fin 2425) =
    MixedData.row202 := by decide +kernel

theorem sourceRowsAt203 : MixedData.sourceRows (203 : Fin 2425) =
    MixedData.row203 := by decide +kernel

theorem sourceRowsAt204 : MixedData.sourceRows (204 : Fin 2425) =
    MixedData.row204 := by decide +kernel

theorem sourceRowsAt205 : MixedData.sourceRows (205 : Fin 2425) =
    MixedData.row205 := by decide +kernel

theorem sourceRowsAt206 : MixedData.sourceRows (206 : Fin 2425) =
    MixedData.row206 := by decide +kernel

theorem sourceRowsAt207 : MixedData.sourceRows (207 : Fin 2425) =
    MixedData.row207 := by decide +kernel

theorem chunkSound12 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 12) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 192 ∨ k.val = 193 ∨ k.val = 194 ∨ k.val = 195 ∨ k.val = 196 ∨ k.val = 197 ∨ k.val = 198 ∨ k.val = 199 ∨ k.val = 200 ∨ k.val = 201 ∨ k.val = 202 ∨ k.val = 203 ∨ k.val = 204 ∨ k.val = 205 ∨ k.val = 206 ∨ k.val = 207 := by omega
  rcases heq with h192 | h193 | h194 | h195 | h196 | h197 | h198 | h199 | h200 | h201 | h202 | h203 | h204 | h205 | h206 | h207
  · have he : k = (192 : Fin 2425) := Fin.ext h192
    subst k
    rw [sourceRowsAt192]
    exact rowSound192 B hB hF
  · have he : k = (193 : Fin 2425) := Fin.ext h193
    subst k
    rw [sourceRowsAt193]
    exact rowSound193 B hB hF
  · have he : k = (194 : Fin 2425) := Fin.ext h194
    subst k
    rw [sourceRowsAt194]
    exact rowSound194 B hB hF
  · have he : k = (195 : Fin 2425) := Fin.ext h195
    subst k
    rw [sourceRowsAt195]
    exact rowSound195 B hB hF
  · have he : k = (196 : Fin 2425) := Fin.ext h196
    subst k
    rw [sourceRowsAt196]
    exact rowSound196 B hB hF
  · have he : k = (197 : Fin 2425) := Fin.ext h197
    subst k
    rw [sourceRowsAt197]
    exact rowSound197 B hB hF
  · have he : k = (198 : Fin 2425) := Fin.ext h198
    subst k
    rw [sourceRowsAt198]
    exact rowSound198 B hB hF
  · have he : k = (199 : Fin 2425) := Fin.ext h199
    subst k
    rw [sourceRowsAt199]
    exact rowSound199 B hB hF
  · have he : k = (200 : Fin 2425) := Fin.ext h200
    subst k
    rw [sourceRowsAt200]
    exact rowSound200 B hB hF
  · have he : k = (201 : Fin 2425) := Fin.ext h201
    subst k
    rw [sourceRowsAt201]
    exact rowSound201 B hB hF
  · have he : k = (202 : Fin 2425) := Fin.ext h202
    subst k
    rw [sourceRowsAt202]
    exact rowSound202 B hB hF
  · have he : k = (203 : Fin 2425) := Fin.ext h203
    subst k
    rw [sourceRowsAt203]
    exact rowSound203 B hB hF
  · have he : k = (204 : Fin 2425) := Fin.ext h204
    subst k
    rw [sourceRowsAt204]
    exact rowSound204 B hB hF
  · have he : k = (205 : Fin 2425) := Fin.ext h205
    subst k
    rw [sourceRowsAt205]
    exact rowSound205 B hB hF
  · have he : k = (206 : Fin 2425) := Fin.ext h206
    subst k
    rw [sourceRowsAt206]
    exact rowSound206 B hB hF
  · have he : k = (207 : Fin 2425) := Fin.ext h207
    subst k
    rw [sourceRowsAt207]
    exact rowSound207 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
