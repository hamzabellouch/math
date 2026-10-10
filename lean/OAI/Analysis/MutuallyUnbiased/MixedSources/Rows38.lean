import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources22

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero608 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource608 (mixedVector B) = 0 := by
  have h2833 : mixedVector B (Sum.inr 2833) = Sparse.eval nodeValue2833 (mixedVector B) := by
    change mixedMoment B node2833 node2833Labels = _
    exact sound2833 B hB hF
  have h2834 : mixedVector B (Sum.inr 2834) = Sparse.eval nodeValue2834 (mixedVector B) := by
    change mixedMoment B node2834 node2834Labels = _
    exact sound2834 B hB hF
  have h2836 : mixedVector B (Sum.inr 2836) = Sparse.eval nodeValue2836 (mixedVector B) := by
    change mixedMoment B node2836 node2836Labels = _
    exact sound2836 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3238 : mixedVector B (Sum.inr 3238) = Sparse.eval nodeValue3238 (mixedVector B) := by
    change mixedMoment B node3238 node3238Labels = _
    exact sound3238 B hB hF
  have h3239 : mixedVector B (Sum.inr 3239) = Sparse.eval nodeValue3239 (mixedVector B) := by
    change mixedMoment B node3239 node3239Labels = _
    exact sound3239 B hB hF
  have h3241 : mixedVector B (Sum.inr 3241) = Sparse.eval nodeValue3241 (mixedVector B) := by
    change mixedMoment B node3241 node3241Labels = _
    exact sound3241 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3460 : mixedVector B (Sum.inr 3460) = Sparse.eval nodeValue3460 (mixedVector B) := by
    change mixedMoment B node3460 node3460Labels = _
    exact sound3460 B hB hF
  have h3461 : mixedVector B (Sum.inr 3461) = Sparse.eval nodeValue3461 (mixedVector B) := by
    change mixedMoment B node3461 node3461Labels = _
    exact sound3461 B hB hF
  have h3464 : mixedVector B (Sum.inr 3464) = Sparse.eval nodeValue3464 (mixedVector B) := by
    change mixedMoment B node3464 node3464Labels = _
    exact sound3464 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3528 : mixedVector B (Sum.inr 3528) = Sparse.eval nodeValue3528 (mixedVector B) := by
    change mixedMoment B node3528 node3528Labels = _
    exact sound3528 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3567 : mixedVector B (Sum.inr 3567) = Sparse.eval nodeValue3567 (mixedVector B) := by
    change mixedMoment B node3567 node3567Labels = _
    exact sound3567 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3847 : mixedVector B (Sum.inr 3847) = Sparse.eval nodeValue3847 (mixedVector B) := by
    change mixedMoment B node3847 node3847Labels = _
    exact sound3847 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853 B hB hF
  simpa only [sourceForm701, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2833, h2834, h2836, h3037, h3238, h3239, h3241, h3289, h3460, h3461, h3464, h3525, h3528, h3534, h3535, h3541, h3567, h3573, h3801, h3847, h3853, reducedSource608] using sourceEq701 B hB

theorem rowSound608 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row608 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck608, numericCheck608, reducedZero608 B hB hF, mul_zero]

theorem reducedZero609 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource609 (mixedVector B) = 0 := by
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h3906 : mixedVector B (Sum.inr 3906) = Sparse.eval nodeValue3906 (mixedVector B) := by
    change mixedMoment B node3906 node3906Labels = _
    exact sound3906 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm702, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2730, h3812, h3906, h4092, reducedSource609] using sourceEq702 B hB

theorem rowSound609 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row609 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck609, numericCheck609, reducedZero609 B hB hF, mul_zero]

theorem reducedZero610 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource610 (mixedVector B) = 0 := by
  have h1276 : mixedVector B (Sum.inr 1276) = Sparse.eval nodeValue1276 (mixedVector B) := by
    change mixedMoment B node1276 node1276Labels = _
    exact sound1276 B hB hF
  have h2645 : mixedVector B (Sum.inr 2645) = Sparse.eval nodeValue2645 (mixedVector B) := by
    change mixedMoment B node2645 node2645Labels = _
    exact sound2645 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h2757 : mixedVector B (Sum.inr 2757) = Sparse.eval nodeValue2757 (mixedVector B) := by
    change mixedMoment B node2757 node2757Labels = _
    exact sound2757 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm704, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1276, h2645, h2730, h2757, h2773, h4092, reducedSource610] using sourceEq704 B hB

theorem rowSound610 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row610 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck610, numericCheck610, reducedZero610 B hB hF, mul_zero]

theorem reducedZero611 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource611 (mixedVector B) = 0 := by
  have h2493 : mixedVector B (Sum.inr 2493) = Sparse.eval nodeValue2493 (mixedVector B) := by
    change mixedMoment B node2493 node2493Labels = _
    exact sound2493 B hB hF
  have h2494 : mixedVector B (Sum.inr 2494) = Sparse.eval nodeValue2494 (mixedVector B) := by
    change mixedMoment B node2494 node2494Labels = _
    exact sound2494 B hB hF
  have h2508 : mixedVector B (Sum.inr 2508) = Sparse.eval nodeValue2508 (mixedVector B) := by
    change mixedMoment B node2508 node2508Labels = _
    exact sound2508 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm705, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2493, h2494, h2508, h2730, h3812, h4092, reducedSource611] using sourceEq705 B hB

theorem rowSound611 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row611 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck611, numericCheck611, reducedZero611 B hB hF, mul_zero]

theorem reducedZero612 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource612 (mixedVector B) = 0 := by
  have h4406 : mixedVector B (Sum.inr 4406) = Sparse.eval nodeValue4406 (mixedVector B) := by
    change mixedMoment B node4406 node4406Labels = _
    exact sound4406 B hB hF
  have h4407 : mixedVector B (Sum.inr 4407) = Sparse.eval nodeValue4407 (mixedVector B) := by
    change mixedMoment B node4407 node4407Labels = _
    exact sound4407 B hB hF
  have h4414 : mixedVector B (Sum.inr 4414) = Sparse.eval nodeValue4414 (mixedVector B) := by
    change mixedMoment B node4414 node4414Labels = _
    exact sound4414 B hB hF
  have h4473 : mixedVector B (Sum.inr 4473) = Sparse.eval nodeValue4473 (mixedVector B) := by
    change mixedMoment B node4473 node4473Labels = _
    exact sound4473 B hB hF
  have h5004 : mixedVector B (Sum.inr 5004) = Sparse.eval nodeValue5004 (mixedVector B) := by
    change mixedMoment B node5004 node5004Labels = _
    exact sound5004 B hB hF
  have h5005 : mixedVector B (Sum.inr 5005) = Sparse.eval nodeValue5005 (mixedVector B) := by
    change mixedMoment B node5005 node5005Labels = _
    exact sound5005 B hB hF
  have h5011 : mixedVector B (Sum.inr 5011) = Sparse.eval nodeValue5011 (mixedVector B) := by
    change mixedMoment B node5011 node5011Labels = _
    exact sound5011 B hB hF
  have h5150 : mixedVector B (Sum.inr 5150) = Sparse.eval nodeValue5150 (mixedVector B) := by
    change mixedMoment B node5150 node5150Labels = _
    exact sound5150 B hB hF
  have h5184 : mixedVector B (Sum.inr 5184) = Sparse.eval nodeValue5184 (mixedVector B) := by
    change mixedMoment B node5184 node5184Labels = _
    exact sound5184 B hB hF
  have h5185 : mixedVector B (Sum.inr 5185) = Sparse.eval nodeValue5185 (mixedVector B) := by
    change mixedMoment B node5185 node5185Labels = _
    exact sound5185 B hB hF
  have h5202 : mixedVector B (Sum.inr 5202) = Sparse.eval nodeValue5202 (mixedVector B) := by
    change mixedMoment B node5202 node5202Labels = _
    exact sound5202 B hB hF
  have h5243 : mixedVector B (Sum.inr 5243) = Sparse.eval nodeValue5243 (mixedVector B) := by
    change mixedMoment B node5243 node5243Labels = _
    exact sound5243 B hB hF
  have h5244 : mixedVector B (Sum.inr 5244) = Sparse.eval nodeValue5244 (mixedVector B) := by
    change mixedMoment B node5244 node5244Labels = _
    exact sound5244 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5266 : mixedVector B (Sum.inr 5266) = Sparse.eval nodeValue5266 (mixedVector B) := by
    change mixedMoment B node5266 node5266Labels = _
    exact sound5266 B hB hF
  have h5270 : mixedVector B (Sum.inr 5270) = Sparse.eval nodeValue5270 (mixedVector B) := by
    change mixedMoment B node5270 node5270Labels = _
    exact sound5270 B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450 B hB hF
  have h5472 : mixedVector B (Sum.inr 5472) = Sparse.eval nodeValue5472 (mixedVector B) := by
    change mixedMoment B node5472 node5472Labels = _
    exact sound5472 B hB hF
  simpa only [sourceForm706, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4406, h4407, h4414, h4473, h5004, h5005, h5011, h5150, h5184, h5185, h5202, h5243, h5244, h5265, h5266, h5270, h5301, h5429, h5431, h5450, h5472, reducedSource612] using sourceEq706 B hB

theorem rowSound612 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row612 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck612, numericCheck612, reducedZero612 B hB hF, mul_zero]

theorem reducedZero613 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource613 (mixedVector B) = 0 := by
  have h987 : mixedVector B (Sum.inr 987) = Sparse.eval nodeValue987 (mixedVector B) := by
    change mixedMoment B node987 node987Labels = _
    exact sound987 B hB hF
  have h988 : mixedVector B (Sum.inr 988) = Sparse.eval nodeValue988 (mixedVector B) := by
    change mixedMoment B node988 node988Labels = _
    exact sound988 B hB hF
  have h995 : mixedVector B (Sum.inr 995) = Sparse.eval nodeValue995 (mixedVector B) := by
    change mixedMoment B node995 node995Labels = _
    exact sound995 B hB hF
  have h1056 : mixedVector B (Sum.inr 1056) = Sparse.eval nodeValue1056 (mixedVector B) := by
    change mixedMoment B node1056 node1056Labels = _
    exact sound1056 B hB hF
  have h2389 : mixedVector B (Sum.inr 2389) = Sparse.eval nodeValue2389 (mixedVector B) := by
    change mixedMoment B node2389 node2389Labels = _
    exact sound2389 B hB hF
  have h2390 : mixedVector B (Sum.inr 2390) = Sparse.eval nodeValue2390 (mixedVector B) := by
    change mixedMoment B node2390 node2390Labels = _
    exact sound2390 B hB hF
  have h2396 : mixedVector B (Sum.inr 2396) = Sparse.eval nodeValue2396 (mixedVector B) := by
    change mixedMoment B node2396 node2396Labels = _
    exact sound2396 B hB hF
  have h2614 : mixedVector B (Sum.inr 2614) = Sparse.eval nodeValue2614 (mixedVector B) := by
    change mixedMoment B node2614 node2614Labels = _
    exact sound2614 B hB hF
  have h2615 : mixedVector B (Sum.inr 2615) = Sparse.eval nodeValue2615 (mixedVector B) := by
    change mixedMoment B node2615 node2615Labels = _
    exact sound2615 B hB hF
  have h2636 : mixedVector B (Sum.inr 2636) = Sparse.eval nodeValue2636 (mixedVector B) := by
    change mixedMoment B node2636 node2636Labels = _
    exact sound2636 B hB hF
  have h2697 : mixedVector B (Sum.inr 2697) = Sparse.eval nodeValue2697 (mixedVector B) := by
    change mixedMoment B node2697 node2697Labels = _
    exact sound2697 B hB hF
  have h2698 : mixedVector B (Sum.inr 2698) = Sparse.eval nodeValue2698 (mixedVector B) := by
    change mixedMoment B node2698 node2698Labels = _
    exact sound2698 B hB hF
  have h2700 : mixedVector B (Sum.inr 2700) = Sparse.eval nodeValue2700 (mixedVector B) := by
    change mixedMoment B node2700 node2700Labels = _
    exact sound2700 B hB hF
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
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h3887 : mixedVector B (Sum.inr 3887) = Sparse.eval nodeValue3887 (mixedVector B) := by
    change mixedMoment B node3887 node3887Labels = _
    exact sound3887 B hB hF
  have h4002 : mixedVector B (Sum.inr 4002) = Sparse.eval nodeValue4002 (mixedVector B) := by
    change mixedMoment B node4002 node4002Labels = _
    exact sound4002 B hB hF
  simpa only [sourceForm707, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h987, h988, h995, h1056, h2389, h2390, h2396, h2614, h2615, h2636, h2697, h2698, h2700, h2730, h2731, h2738, h2775, h3874, h3875, h3887, h4002, reducedSource613] using sourceEq707 B hB

theorem rowSound613 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row613 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck613, numericCheck613, reducedZero613 B hB hF, mul_zero]

theorem reducedZero614 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource614 (mixedVector B) = 0 := by
  have h1593 : mixedVector B (Sum.inr 1593) = Sparse.eval nodeValue1593 (mixedVector B) := by
    change mixedMoment B node1593 node1593Labels = _
    exact sound1593 B hB hF
  have h1594 : mixedVector B (Sum.inr 1594) = Sparse.eval nodeValue1594 (mixedVector B) := by
    change mixedMoment B node1594 node1594Labels = _
    exact sound1594 B hB hF
  have h1601 : mixedVector B (Sum.inr 1601) = Sparse.eval nodeValue1601 (mixedVector B) := by
    change mixedMoment B node1601 node1601Labels = _
    exact sound1601 B hB hF
  have h1699 : mixedVector B (Sum.inr 1699) = Sparse.eval nodeValue1699 (mixedVector B) := by
    change mixedMoment B node1699 node1699Labels = _
    exact sound1699 B hB hF
  have h2912 : mixedVector B (Sum.inr 2912) = Sparse.eval nodeValue2912 (mixedVector B) := by
    change mixedMoment B node2912 node2912Labels = _
    exact sound2912 B hB hF
  have h2923 : mixedVector B (Sum.inr 2923) = Sparse.eval nodeValue2923 (mixedVector B) := by
    change mixedMoment B node2923 node2923Labels = _
    exact sound2923 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3337 : mixedVector B (Sum.inr 3337) = Sparse.eval nodeValue3337 (mixedVector B) := by
    change mixedMoment B node3337 node3337Labels = _
    exact sound3337 B hB hF
  have h3342 : mixedVector B (Sum.inr 3342) = Sparse.eval nodeValue3342 (mixedVector B) := by
    change mixedMoment B node3342 node3342Labels = _
    exact sound3342 B hB hF
  have h3488 : mixedVector B (Sum.inr 3488) = Sparse.eval nodeValue3488 (mixedVector B) := by
    change mixedMoment B node3488 node3488Labels = _
    exact sound3488 B hB hF
  have h3497 : mixedVector B (Sum.inr 3497) = Sparse.eval nodeValue3497 (mixedVector B) := by
    change mixedMoment B node3497 node3497Labels = _
    exact sound3497 B hB hF
  have h3524 : mixedVector B (Sum.inr 3524) = Sparse.eval nodeValue3524 (mixedVector B) := by
    change mixedMoment B node3524 node3524Labels = _
    exact sound3524 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3529 : mixedVector B (Sum.inr 3529) = Sparse.eval nodeValue3529 (mixedVector B) := by
    change mixedMoment B node3529 node3529Labels = _
    exact sound3529 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3617 : mixedVector B (Sum.inr 3617) = Sparse.eval nodeValue3617 (mixedVector B) := by
    change mixedMoment B node3617 node3617Labels = _
    exact sound3617 B hB hF
  have h3619 : mixedVector B (Sum.inr 3619) = Sparse.eval nodeValue3619 (mixedVector B) := by
    change mixedMoment B node3619 node3619Labels = _
    exact sound3619 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h4026 : mixedVector B (Sum.inr 4026) = Sparse.eval nodeValue4026 (mixedVector B) := by
    change mixedMoment B node4026 node4026Labels = _
    exact sound4026 B hB hF
  have h4029 : mixedVector B (Sum.inr 4029) = Sparse.eval nodeValue4029 (mixedVector B) := by
    change mixedMoment B node4029 node4029Labels = _
    exact sound4029 B hB hF
  simpa only [sourceForm708, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1593, h1594, h1601, h1699, h2912, h2923, h3075, h3337, h3342, h3488, h3497, h3524, h3526, h3529, h3535, h3617, h3619, h3954, h3957, h4026, h4029, reducedSource614] using sourceEq708 B hB

theorem rowSound614 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row614 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck614, numericCheck614, reducedZero614 B hB hF, mul_zero]

theorem reducedZero615 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource615 (mixedVector B) = 0 := by
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h3910 : mixedVector B (Sum.inr 3910) = Sparse.eval nodeValue3910 (mixedVector B) := by
    change mixedMoment B node3910 node3910Labels = _
    exact sound3910 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm709, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3037, h3846, h3849, h3910, h3957, h4091, reducedSource615] using sourceEq709 B hB

theorem rowSound615 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row615 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck615, numericCheck615, reducedZero615 B hB hF, mul_zero]

theorem reducedZero616 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource616 (mixedVector B) = 0 := by
  have h1358 : mixedVector B (Sum.inr 1358) = Sparse.eval nodeValue1358 (mixedVector B) := by
    change mixedMoment B node1358 node1358Labels = _
    exact sound1358 B hB hF
  have h1360 : mixedVector B (Sum.inr 1360) = Sparse.eval nodeValue1360 (mixedVector B) := by
    change mixedMoment B node1360 node1360Labels = _
    exact sound1360 B hB hF
  have h1366 : mixedVector B (Sum.inr 1366) = Sparse.eval nodeValue1366 (mixedVector B) := by
    change mixedMoment B node1366 node1366Labels = _
    exact sound1366 B hB hF
  have h1421 : mixedVector B (Sum.inr 1421) = Sparse.eval nodeValue1421 (mixedVector B) := by
    change mixedMoment B node1421 node1421Labels = _
    exact sound1421 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm710, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1358, h1360, h1366, h1421, h3037, h4091, reducedSource616] using sourceEq710 B hB

theorem rowSound616 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row616 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck616, numericCheck616, reducedZero616 B hB hF, mul_zero]

theorem reducedZero617 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource617 (mixedVector B) = 0 := by
  have h1366 : mixedVector B (Sum.inr 1366) = Sparse.eval nodeValue1366 (mixedVector B) := by
    change mixedMoment B node1366 node1366Labels = _
    exact sound1366 B hB hF
  have h2880 : mixedVector B (Sum.inr 2880) = Sparse.eval nodeValue2880 (mixedVector B) := by
    change mixedMoment B node2880 node2880Labels = _
    exact sound2880 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm711, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1366, h2880, h3037, h3053, h4091, reducedSource617] using sourceEq711 B hB

theorem rowSound617 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row617 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck617, numericCheck617, reducedZero617 B hB hF, mul_zero]

theorem reducedZero618 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource618 (mixedVector B) = 0 := by
  have h2862 : mixedVector B (Sum.inr 2862) = Sparse.eval nodeValue2862 (mixedVector B) := by
    change mixedMoment B node2862 node2862Labels = _
    exact sound2862 B hB hF
  have h2864 : mixedVector B (Sum.inr 2864) = Sparse.eval nodeValue2864 (mixedVector B) := by
    change mixedMoment B node2864 node2864Labels = _
    exact sound2864 B hB hF
  have h2880 : mixedVector B (Sum.inr 2880) = Sparse.eval nodeValue2880 (mixedVector B) := by
    change mixedMoment B node2880 node2880Labels = _
    exact sound2880 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm713, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2862, h2864, h2880, h3037, h3957, h4091, reducedSource618] using sourceEq713 B hB

theorem rowSound618 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row618 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck618, numericCheck618, reducedZero618 B hB hF, mul_zero]

theorem reducedZero619 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource619 (mixedVector B) = 0 := by
  have h2573 : mixedVector B (Sum.inr 2573) = Sparse.eval nodeValue2573 (mixedVector B) := by
    change mixedMoment B node2573 node2573Labels = _
    exact sound2573 B hB hF
  have h3029 : mixedVector B (Sum.inr 3029) = Sparse.eval nodeValue3029 (mixedVector B) := by
    change mixedMoment B node3029 node3029Labels = _
    exact sound3029 B hB hF
  have h3030 : mixedVector B (Sum.inr 3030) = Sparse.eval nodeValue3030 (mixedVector B) := by
    change mixedMoment B node3030 node3030Labels = _
    exact sound3030 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm714, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2573, h3029, h3030, h3037, h3849, h4091, reducedSource619] using sourceEq714 B hB

theorem rowSound619 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row619 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck619, numericCheck619, reducedZero619 B hB hF, mul_zero]

theorem reducedZero620 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource620 (mixedVector B) = 0 := by
  have h4793 : mixedVector B (Sum.inr 4793) = Sparse.eval nodeValue4793 (mixedVector B) := by
    change mixedMoment B node4793 node4793Labels = _
    exact sound4793 B hB hF
  have h4794 : mixedVector B (Sum.inr 4794) = Sparse.eval nodeValue4794 (mixedVector B) := by
    change mixedMoment B node4794 node4794Labels = _
    exact sound4794 B hB hF
  have h4795 : mixedVector B (Sum.inr 4795) = Sparse.eval nodeValue4795 (mixedVector B) := by
    change mixedMoment B node4795 node4795Labels = _
    exact sound4795 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4806 : mixedVector B (Sum.inr 4806) = Sparse.eval nodeValue4806 (mixedVector B) := by
    change mixedMoment B node4806 node4806Labels = _
    exact sound4806 B hB hF
  have h4878 : mixedVector B (Sum.inr 4878) = Sparse.eval nodeValue4878 (mixedVector B) := by
    change mixedMoment B node4878 node4878Labels = _
    exact sound4878 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h5226 : mixedVector B (Sum.inr 5226) = Sparse.eval nodeValue5226 (mixedVector B) := by
    change mixedMoment B node5226 node5226Labels = _
    exact sound5226 B hB hF
  have h5227 : mixedVector B (Sum.inr 5227) = Sparse.eval nodeValue5227 (mixedVector B) := by
    change mixedMoment B node5227 node5227Labels = _
    exact sound5227 B hB hF
  have h5230 : mixedVector B (Sum.inr 5230) = Sparse.eval nodeValue5230 (mixedVector B) := by
    change mixedMoment B node5230 node5230Labels = _
    exact sound5230 B hB hF
  have h5231 : mixedVector B (Sum.inr 5231) = Sparse.eval nodeValue5231 (mixedVector B) := by
    change mixedMoment B node5231 node5231Labels = _
    exact sound5231 B hB hF
  have h5256 : mixedVector B (Sum.inr 5256) = Sparse.eval nodeValue5256 (mixedVector B) := by
    change mixedMoment B node5256 node5256Labels = _
    exact sound5256 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5262 : mixedVector B (Sum.inr 5262) = Sparse.eval nodeValue5262 (mixedVector B) := by
    change mixedMoment B node5262 node5262Labels = _
    exact sound5262 B hB hF
  have h5263 : mixedVector B (Sum.inr 5263) = Sparse.eval nodeValue5263 (mixedVector B) := by
    change mixedMoment B node5263 node5263Labels = _
    exact sound5263 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5299 : mixedVector B (Sum.inr 5299) = Sparse.eval nodeValue5299 (mixedVector B) := by
    change mixedMoment B node5299 node5299Labels = _
    exact sound5299 B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  simpa only [sourceForm715, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4793, h4794, h4795, h4805, h4806, h4878, h4889, h5226, h5227, h5230, h5231, h5256, h5257, h5262, h5263, h5265, h5292, h5299, h5301, reducedSource620] using sourceEq715 B hB

theorem rowSound620 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row620 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck620, numericCheck620, reducedZero620 B hB hF, mul_zero]

theorem reducedZero621 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource621 (mixedVector B) = 0 := by
  have h2117 : mixedVector B (Sum.inr 2117) = Sparse.eval nodeValue2117 (mixedVector B) := by
    change mixedMoment B node2117 node2117Labels = _
    exact sound2117 B hB hF
  have h2118 : mixedVector B (Sum.inr 2118) = Sparse.eval nodeValue2118 (mixedVector B) := by
    change mixedMoment B node2118 node2118Labels = _
    exact sound2118 B hB hF
  have h2131 : mixedVector B (Sum.inr 2131) = Sparse.eval nodeValue2131 (mixedVector B) := by
    change mixedMoment B node2131 node2131Labels = _
    exact sound2131 B hB hF
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h2214 : mixedVector B (Sum.inr 2214) = Sparse.eval nodeValue2214 (mixedVector B) := by
    change mixedMoment B node2214 node2214Labels = _
    exact sound2214 B hB hF
  have h2219 : mixedVector B (Sum.inr 2219) = Sparse.eval nodeValue2219 (mixedVector B) := by
    change mixedMoment B node2219 node2219Labels = _
    exact sound2219 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h2675 : mixedVector B (Sum.inr 2675) = Sparse.eval nodeValue2675 (mixedVector B) := by
    change mixedMoment B node2675 node2675Labels = _
    exact sound2675 B hB hF
  have h2676 : mixedVector B (Sum.inr 2676) = Sparse.eval nodeValue2676 (mixedVector B) := by
    change mixedMoment B node2676 node2676Labels = _
    exact sound2676 B hB hF
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2727 : mixedVector B (Sum.inr 2727) = Sparse.eval nodeValue2727 (mixedVector B) := by
    change mixedMoment B node2727 node2727Labels = _
    exact sound2727 B hB hF
  have h2728 : mixedVector B (Sum.inr 2728) = Sparse.eval nodeValue2728 (mixedVector B) := by
    change mixedMoment B node2728 node2728Labels = _
    exact sound2728 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2775 : mixedVector B (Sum.inr 2775) = Sparse.eval nodeValue2775 (mixedVector B) := by
    change mixedMoment B node2775 node2775Labels = _
    exact sound2775 B hB hF
  have h3043 : mixedVector B (Sum.inr 3043) = Sparse.eval nodeValue3043 (mixedVector B) := by
    change mixedMoment B node3043 node3043Labels = _
    exact sound3043 B hB hF
  have h3087 : mixedVector B (Sum.inr 3087) = Sparse.eval nodeValue3087 (mixedVector B) := by
    change mixedMoment B node3087 node3087Labels = _
    exact sound3087 B hB hF
  have h3091 : mixedVector B (Sum.inr 3091) = Sparse.eval nodeValue3091 (mixedVector B) := by
    change mixedMoment B node3091 node3091Labels = _
    exact sound3091 B hB hF
  have h3093 : mixedVector B (Sum.inr 3093) = Sparse.eval nodeValue3093 (mixedVector B) := by
    change mixedMoment B node3093 node3093Labels = _
    exact sound3093 B hB hF
  simpa only [sourceForm716, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2117, h2118, h2131, h2213, h2214, h2219, h2277, h2675, h2676, h2720, h2721, h2727, h2728, h2730, h2766, h2773, h2775, h3043, h3087, h3091, h3093, reducedSource621] using sourceEq716 B hB

theorem rowSound621 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row621 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck621, numericCheck621, reducedZero621 B hB hF, mul_zero]

theorem reducedZero622 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource622 (mixedVector B) = 0 := by
  have h2010 : mixedVector B (Sum.inr 2010) = Sparse.eval nodeValue2010 (mixedVector B) := by
    change mixedMoment B node2010 node2010Labels = _
    exact sound2010 B hB hF
  have h2011 : mixedVector B (Sum.inr 2011) = Sparse.eval nodeValue2011 (mixedVector B) := by
    change mixedMoment B node2011 node2011Labels = _
    exact sound2011 B hB hF
  have h2024 : mixedVector B (Sum.inr 2024) = Sparse.eval nodeValue2024 (mixedVector B) := by
    change mixedMoment B node2024 node2024Labels = _
    exact sound2024 B hB hF
  have h2234 : mixedVector B (Sum.inr 2234) = Sparse.eval nodeValue2234 (mixedVector B) := by
    change mixedMoment B node2234 node2234Labels = _
    exact sound2234 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2671 : mixedVector B (Sum.inr 2671) = Sparse.eval nodeValue2671 (mixedVector B) := by
    change mixedMoment B node2671 node2671Labels = _
    exact sound2671 B hB hF
  have h2676 : mixedVector B (Sum.inr 2676) = Sparse.eval nodeValue2676 (mixedVector B) := by
    change mixedMoment B node2676 node2676Labels = _
    exact sound2676 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h3034 : mixedVector B (Sum.inr 3034) = Sparse.eval nodeValue3034 (mixedVector B) := by
    change mixedMoment B node3034 node3034Labels = _
    exact sound3034 B hB hF
  have h3036 : mixedVector B (Sum.inr 3036) = Sparse.eval nodeValue3036 (mixedVector B) := by
    change mixedMoment B node3036 node3036Labels = _
    exact sound3036 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3041 : mixedVector B (Sum.inr 3041) = Sparse.eval nodeValue3041 (mixedVector B) := by
    change mixedMoment B node3041 node3041Labels = _
    exact sound3041 B hB hF
  have h3043 : mixedVector B (Sum.inr 3043) = Sparse.eval nodeValue3043 (mixedVector B) := by
    change mixedMoment B node3043 node3043Labels = _
    exact sound3043 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  have h3085 : mixedVector B (Sum.inr 3085) = Sparse.eval nodeValue3085 (mixedVector B) := by
    change mixedMoment B node3085 node3085Labels = _
    exact sound3085 B hB hF
  have h3087 : mixedVector B (Sum.inr 3087) = Sparse.eval nodeValue3087 (mixedVector B) := by
    change mixedMoment B node3087 node3087Labels = _
    exact sound3087 B hB hF
  have h3100 : mixedVector B (Sum.inr 3100) = Sparse.eval nodeValue3100 (mixedVector B) := by
    change mixedMoment B node3100 node3100Labels = _
    exact sound3100 B hB hF
  have h3199 : mixedVector B (Sum.inr 3199) = Sparse.eval nodeValue3199 (mixedVector B) := by
    change mixedMoment B node3199 node3199Labels = _
    exact sound3199 B hB hF
  have h3203 : mixedVector B (Sum.inr 3203) = Sparse.eval nodeValue3203 (mixedVector B) := by
    change mixedMoment B node3203 node3203Labels = _
    exact sound3203 B hB hF
  have h3223 : mixedVector B (Sum.inr 3223) = Sparse.eval nodeValue3223 (mixedVector B) := by
    change mixedMoment B node3223 node3223Labels = _
    exact sound3223 B hB hF
  simpa only [sourceForm717, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2010, h2011, h2024, h2234, h2669, h2671, h2676, h2721, h3034, h3036, h3037, h3041, h3043, h3051, h3053, h3085, h3087, h3100, h3199, h3203, h3223, reducedSource622] using sourceEq717 B hB

theorem rowSound622 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row622 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck622, numericCheck622, reducedZero622 B hB hF, mul_zero]

theorem reducedZero623 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource623 (mixedVector B) = 0 := by
  have h3376 : mixedVector B (Sum.inr 3376) = Sparse.eval nodeValue3376 (mixedVector B) := by
    change mixedMoment B node3376 node3376Labels = _
    exact sound3376 B hB hF
  have h3378 : mixedVector B (Sum.inr 3378) = Sparse.eval nodeValue3378 (mixedVector B) := by
    change mixedMoment B node3378 node3378Labels = _
    exact sound3378 B hB hF
  have h3390 : mixedVector B (Sum.inr 3390) = Sparse.eval nodeValue3390 (mixedVector B) := by
    change mixedMoment B node3390 node3390Labels = _
    exact sound3390 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3532 : mixedVector B (Sum.inr 3532) = Sparse.eval nodeValue3532 (mixedVector B) := by
    change mixedMoment B node3532 node3532Labels = _
    exact sound3532 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm718, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3376, h3378, h3390, h3526, h3532, h4083, reducedSource623] using sourceEq718 B hB

theorem rowSound623 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row623 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck623, numericCheck623, reducedZero623 B hB hF, mul_zero]

theorem sourceRowsAt608 : MixedData.sourceRows (608 : Fin 2425) =
    MixedData.row608 := by decide +kernel

theorem sourceRowsAt609 : MixedData.sourceRows (609 : Fin 2425) =
    MixedData.row609 := by decide +kernel

theorem sourceRowsAt610 : MixedData.sourceRows (610 : Fin 2425) =
    MixedData.row610 := by decide +kernel

theorem sourceRowsAt611 : MixedData.sourceRows (611 : Fin 2425) =
    MixedData.row611 := by decide +kernel

theorem sourceRowsAt612 : MixedData.sourceRows (612 : Fin 2425) =
    MixedData.row612 := by decide +kernel

theorem sourceRowsAt613 : MixedData.sourceRows (613 : Fin 2425) =
    MixedData.row613 := by decide +kernel

theorem sourceRowsAt614 : MixedData.sourceRows (614 : Fin 2425) =
    MixedData.row614 := by decide +kernel

theorem sourceRowsAt615 : MixedData.sourceRows (615 : Fin 2425) =
    MixedData.row615 := by decide +kernel

theorem sourceRowsAt616 : MixedData.sourceRows (616 : Fin 2425) =
    MixedData.row616 := by decide +kernel

theorem sourceRowsAt617 : MixedData.sourceRows (617 : Fin 2425) =
    MixedData.row617 := by decide +kernel

theorem sourceRowsAt618 : MixedData.sourceRows (618 : Fin 2425) =
    MixedData.row618 := by decide +kernel

theorem sourceRowsAt619 : MixedData.sourceRows (619 : Fin 2425) =
    MixedData.row619 := by decide +kernel

theorem sourceRowsAt620 : MixedData.sourceRows (620 : Fin 2425) =
    MixedData.row620 := by decide +kernel

theorem sourceRowsAt621 : MixedData.sourceRows (621 : Fin 2425) =
    MixedData.row621 := by decide +kernel

theorem sourceRowsAt622 : MixedData.sourceRows (622 : Fin 2425) =
    MixedData.row622 := by decide +kernel

theorem sourceRowsAt623 : MixedData.sourceRows (623 : Fin 2425) =
    MixedData.row623 := by decide +kernel

theorem chunkSound38 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 38) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 608 ∨ k.val = 609 ∨ k.val = 610 ∨ k.val = 611 ∨ k.val = 612 ∨ k.val = 613 ∨ k.val = 614 ∨ k.val = 615 ∨ k.val = 616 ∨ k.val = 617 ∨ k.val = 618 ∨ k.val = 619 ∨ k.val = 620 ∨ k.val = 621 ∨ k.val = 622 ∨ k.val = 623 := by omega
  rcases heq with h608 | h609 | h610 | h611 | h612 | h613 | h614 | h615 | h616 | h617 | h618 | h619 | h620 | h621 | h622 | h623
  · have he : k = (608 : Fin 2425) := Fin.ext h608
    subst k
    rw [sourceRowsAt608]
    exact rowSound608 B hB hF
  · have he : k = (609 : Fin 2425) := Fin.ext h609
    subst k
    rw [sourceRowsAt609]
    exact rowSound609 B hB hF
  · have he : k = (610 : Fin 2425) := Fin.ext h610
    subst k
    rw [sourceRowsAt610]
    exact rowSound610 B hB hF
  · have he : k = (611 : Fin 2425) := Fin.ext h611
    subst k
    rw [sourceRowsAt611]
    exact rowSound611 B hB hF
  · have he : k = (612 : Fin 2425) := Fin.ext h612
    subst k
    rw [sourceRowsAt612]
    exact rowSound612 B hB hF
  · have he : k = (613 : Fin 2425) := Fin.ext h613
    subst k
    rw [sourceRowsAt613]
    exact rowSound613 B hB hF
  · have he : k = (614 : Fin 2425) := Fin.ext h614
    subst k
    rw [sourceRowsAt614]
    exact rowSound614 B hB hF
  · have he : k = (615 : Fin 2425) := Fin.ext h615
    subst k
    rw [sourceRowsAt615]
    exact rowSound615 B hB hF
  · have he : k = (616 : Fin 2425) := Fin.ext h616
    subst k
    rw [sourceRowsAt616]
    exact rowSound616 B hB hF
  · have he : k = (617 : Fin 2425) := Fin.ext h617
    subst k
    rw [sourceRowsAt617]
    exact rowSound617 B hB hF
  · have he : k = (618 : Fin 2425) := Fin.ext h618
    subst k
    rw [sourceRowsAt618]
    exact rowSound618 B hB hF
  · have he : k = (619 : Fin 2425) := Fin.ext h619
    subst k
    rw [sourceRowsAt619]
    exact rowSound619 B hB hF
  · have he : k = (620 : Fin 2425) := Fin.ext h620
    subst k
    rw [sourceRowsAt620]
    exact rowSound620 B hB hF
  · have he : k = (621 : Fin 2425) := Fin.ext h621
    subst k
    rw [sourceRowsAt621]
    exact rowSound621 B hB hF
  · have he : k = (622 : Fin 2425) := Fin.ext h622
    subst k
    rw [sourceRowsAt622]
    exact rowSound622 B hB hF
  · have he : k = (623 : Fin 2425) := Fin.ext h623
    subst k
    rw [sourceRowsAt623]
    exact rowSound623 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
