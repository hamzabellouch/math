import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources25

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero688 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource688 (mixedVector B) = 0 := by
  have h2457 : mixedVector B (Sum.inr 2457) = Sparse.eval nodeValue2457 (mixedVector B) := by
    change mixedMoment B node2457 node2457Labels = _
    exact sound2457 B hB hF
  have h2460 : mixedVector B (Sum.inr 2460) = Sparse.eval nodeValue2460 (mixedVector B) := by
    change mixedMoment B node2460 node2460Labels = _
    exact sound2460 B hB hF
  have h2507 : mixedVector B (Sum.inr 2507) = Sparse.eval nodeValue2507 (mixedVector B) := by
    change mixedMoment B node2507 node2507Labels = _
    exact sound2507 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h3278 : mixedVector B (Sum.inr 3278) = Sparse.eval nodeValue3278 (mixedVector B) := by
    change mixedMoment B node3278 node3278Labels = _
    exact sound3278 B hB hF
  have h3282 : mixedVector B (Sum.inr 3282) = Sparse.eval nodeValue3282 (mixedVector B) := by
    change mixedMoment B node3282 node3282Labels = _
    exact sound3282 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h3532 : mixedVector B (Sum.inr 3532) = Sparse.eval nodeValue3532 (mixedVector B) := by
    change mixedMoment B node3532 node3532Labels = _
    exact sound3532 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3568 : mixedVector B (Sum.inr 3568) = Sparse.eval nodeValue3568 (mixedVector B) := by
    change mixedMoment B node3568 node3568Labels = _
    exact sound3568 B hB hF
  have h3569 : mixedVector B (Sum.inr 3569) = Sparse.eval nodeValue3569 (mixedVector B) := by
    change mixedMoment B node3569 node3569Labels = _
    exact sound3569 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3574 : mixedVector B (Sum.inr 3574) = Sparse.eval nodeValue3574 (mixedVector B) := by
    change mixedMoment B node3574 node3574Labels = _
    exact sound3574 B hB hF
  have h3576 : mixedVector B (Sum.inr 3576) = Sparse.eval nodeValue3576 (mixedVector B) := by
    change mixedMoment B node3576 node3576Labels = _
    exact sound3576 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  have h3851 : mixedVector B (Sum.inr 3851) = Sparse.eval nodeValue3851 (mixedVector B) := by
    change mixedMoment B node3851 node3851Labels = _
    exact sound3851 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3882 : mixedVector B (Sum.inr 3882) = Sparse.eval nodeValue3882 (mixedVector B) := by
    change mixedMoment B node3882 node3882Labels = _
    exact sound3882 B hB hF
  have h3887 : mixedVector B (Sum.inr 3887) = Sparse.eval nodeValue3887 (mixedVector B) := by
    change mixedMoment B node3887 node3887Labels = _
    exact sound3887 B hB hF
  simpa only [sourceForm796, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2457, h2460, h2507, h2738, h3278, h3282, h3289, h3531, h3532, h3539, h3568, h3569, h3571, h3574, h3576, h3580, h3581, h3851, h3880, h3882, h3887, reducedSource688] using sourceEq796 B hB

theorem rowSound688 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row688 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck688, numericCheck688, reducedZero688 B hB hF, mul_zero]

theorem reducedZero689 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource689 (mixedVector B) = 0 := by
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3901 : mixedVector B (Sum.inr 3901) = Sparse.eval nodeValue3901 (mixedVector B) := by
    change mixedMoment B node3901 node3901Labels = _
    exact sound3901 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  have h3910 : mixedVector B (Sum.inr 3910) = Sparse.eval nodeValue3910 (mixedVector B) := by
    change mixedMoment B node3910 node3910Labels = _
    exact sound3910 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm797, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2750, h3880, h3901, h3909, h3910, h4091, reducedSource689] using sourceEq797 B hB

theorem rowSound689 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row689 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck689, numericCheck689, reducedZero689 B hB hF, mul_zero]

theorem reducedZero690 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource690 (mixedVector B) = 0 := by
  have h1247 : mixedVector B (Sum.inr 1247) = Sparse.eval nodeValue1247 (mixedVector B) := by
    change mixedMoment B node1247 node1247Labels = _
    exact sound1247 B hB hF
  have h1248 : mixedVector B (Sum.inr 1248) = Sparse.eval nodeValue1248 (mixedVector B) := by
    change mixedMoment B node1248 node1248Labels = _
    exact sound1248 B hB hF
  have h1250 : mixedVector B (Sum.inr 1250) = Sparse.eval nodeValue1250 (mixedVector B) := by
    change mixedMoment B node1250 node1250Labels = _
    exact sound1250 B hB hF
  have h1260 : mixedVector B (Sum.inr 1260) = Sparse.eval nodeValue1260 (mixedVector B) := by
    change mixedMoment B node1260 node1260Labels = _
    exact sound1260 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm798, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1247, h1248, h1250, h1260, h2750, h4091, reducedSource690] using sourceEq798 B hB

theorem rowSound690 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row690 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck690, numericCheck690, reducedZero690 B hB hF, mul_zero]

theorem reducedZero691 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource691 (mixedVector B) = 0 := by
  have h1260 : mixedVector B (Sum.inr 1260) = Sparse.eval nodeValue1260 (mixedVector B) := by
    change mixedMoment B node1260 node1260Labels = _
    exact sound1260 B hB hF
  have h2631 : mixedVector B (Sum.inr 2631) = Sparse.eval nodeValue2631 (mixedVector B) := by
    change mixedMoment B node2631 node2631Labels = _
    exact sound2631 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm799, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1260, h2631, h2721, h2750, h2764, h4091, reducedSource691] using sourceEq799 B hB

theorem rowSound691 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row691 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck691, numericCheck691, reducedZero691 B hB hF, mul_zero]

theorem reducedZero692 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource692 (mixedVector B) = 0 := by
  have h2622 : mixedVector B (Sum.inr 2622) = Sparse.eval nodeValue2622 (mixedVector B) := by
    change mixedMoment B node2622 node2622Labels = _
    exact sound2622 B hB hF
  have h2623 : mixedVector B (Sum.inr 2623) = Sparse.eval nodeValue2623 (mixedVector B) := by
    change mixedMoment B node2623 node2623Labels = _
    exact sound2623 B hB hF
  have h2625 : mixedVector B (Sum.inr 2625) = Sparse.eval nodeValue2625 (mixedVector B) := by
    change mixedMoment B node2625 node2625Labels = _
    exact sound2625 B hB hF
  have h2631 : mixedVector B (Sum.inr 2631) = Sparse.eval nodeValue2631 (mixedVector B) := by
    change mixedMoment B node2631 node2631Labels = _
    exact sound2631 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm800, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2622, h2623, h2625, h2631, h2750, h3880, h4091, reducedSource692] using sourceEq800 B hB

theorem rowSound692 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row692 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck692, numericCheck692, reducedZero692 B hB hF, mul_zero]

theorem reducedZero693 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource693 (mixedVector B) = 0 := by
  have h4435 : mixedVector B (Sum.inr 4435) = Sparse.eval nodeValue4435 (mixedVector B) := by
    change mixedMoment B node4435 node4435Labels = _
    exact sound4435 B hB hF
  have h4436 : mixedVector B (Sum.inr 4436) = Sparse.eval nodeValue4436 (mixedVector B) := by
    change mixedMoment B node4436 node4436Labels = _
    exact sound4436 B hB hF
  have h4439 : mixedVector B (Sum.inr 4439) = Sparse.eval nodeValue4439 (mixedVector B) := by
    change mixedMoment B node4439 node4439Labels = _
    exact sound4439 B hB hF
  have h4449 : mixedVector B (Sum.inr 4449) = Sparse.eval nodeValue4449 (mixedVector B) := by
    change mixedMoment B node4449 node4449Labels = _
    exact sound4449 B hB hF
  have h5144 : mixedVector B (Sum.inr 5144) = Sparse.eval nodeValue5144 (mixedVector B) := by
    change mixedMoment B node5144 node5144Labels = _
    exact sound5144 B hB hF
  have h5145 : mixedVector B (Sum.inr 5145) = Sparse.eval nodeValue5145 (mixedVector B) := by
    change mixedMoment B node5145 node5145Labels = _
    exact sound5145 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5160 : mixedVector B (Sum.inr 5160) = Sparse.eval nodeValue5160 (mixedVector B) := by
    change mixedMoment B node5160 node5160Labels = _
    exact sound5160 B hB hF
  have h5219 : mixedVector B (Sum.inr 5219) = Sparse.eval nodeValue5219 (mixedVector B) := by
    change mixedMoment B node5219 node5219Labels = _
    exact sound5219 B hB hF
  have h5220 : mixedVector B (Sum.inr 5220) = Sparse.eval nodeValue5220 (mixedVector B) := by
    change mixedMoment B node5220 node5220Labels = _
    exact sound5220 B hB hF
  have h5226 : mixedVector B (Sum.inr 5226) = Sparse.eval nodeValue5226 (mixedVector B) := by
    change mixedMoment B node5226 node5226Labels = _
    exact sound5226 B hB hF
  have h5249 : mixedVector B (Sum.inr 5249) = Sparse.eval nodeValue5249 (mixedVector B) := by
    change mixedMoment B node5249 node5249Labels = _
    exact sound5249 B hB hF
  have h5251 : mixedVector B (Sum.inr 5251) = Sparse.eval nodeValue5251 (mixedVector B) := by
    change mixedMoment B node5251 node5251Labels = _
    exact sound5251 B hB hF
  have h5255 : mixedVector B (Sum.inr 5255) = Sparse.eval nodeValue5255 (mixedVector B) := by
    change mixedMoment B node5255 node5255Labels = _
    exact sound5255 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5289 : mixedVector B (Sum.inr 5289) = Sparse.eval nodeValue5289 (mixedVector B) := by
    change mixedMoment B node5289 node5289Labels = _
    exact sound5289 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5478 : mixedVector B (Sum.inr 5478) = Sparse.eval nodeValue5478 (mixedVector B) := by
    change mixedMoment B node5478 node5478Labels = _
    exact sound5478 B hB hF
  have h5481 : mixedVector B (Sum.inr 5481) = Sparse.eval nodeValue5481 (mixedVector B) := by
    change mixedMoment B node5481 node5481Labels = _
    exact sound5481 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485 B hB hF
  simpa only [sourceForm801, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4435, h4436, h4439, h4449, h5144, h5145, h5149, h5160, h5219, h5220, h5226, h5249, h5251, h5255, h5282, h5284, h5289, h5431, h5478, h5481, h5485, reducedSource693] using sourceEq801 B hB

theorem rowSound693 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row693 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck693, numericCheck693, reducedZero693 B hB hF, mul_zero]

theorem reducedZero694 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource694 (mixedVector B) = 0 := by
  have h1017 : mixedVector B (Sum.inr 1017) = Sparse.eval nodeValue1017 (mixedVector B) := by
    change mixedMoment B node1017 node1017Labels = _
    exact sound1017 B hB hF
  have h1018 : mixedVector B (Sum.inr 1018) = Sparse.eval nodeValue1018 (mixedVector B) := by
    change mixedMoment B node1018 node1018Labels = _
    exact sound1018 B hB hF
  have h1021 : mixedVector B (Sum.inr 1021) = Sparse.eval nodeValue1021 (mixedVector B) := by
    change mixedMoment B node1021 node1021Labels = _
    exact sound1021 B hB hF
  have h1032 : mixedVector B (Sum.inr 1032) = Sparse.eval nodeValue1032 (mixedVector B) := by
    change mixedMoment B node1032 node1032Labels = _
    exact sound1032 B hB hF
  have h2566 : mixedVector B (Sum.inr 2566) = Sparse.eval nodeValue2566 (mixedVector B) := by
    change mixedMoment B node2566 node2566Labels = _
    exact sound2566 B hB hF
  have h2567 : mixedVector B (Sum.inr 2567) = Sparse.eval nodeValue2567 (mixedVector B) := by
    change mixedMoment B node2567 node2567Labels = _
    exact sound2567 B hB hF
  have h2570 : mixedVector B (Sum.inr 2570) = Sparse.eval nodeValue2570 (mixedVector B) := by
    change mixedMoment B node2570 node2570Labels = _
    exact sound2570 B hB hF
  have h2587 : mixedVector B (Sum.inr 2587) = Sparse.eval nodeValue2587 (mixedVector B) := by
    change mixedMoment B node2587 node2587Labels = _
    exact sound2587 B hB hF
  have h2661 : mixedVector B (Sum.inr 2661) = Sparse.eval nodeValue2661 (mixedVector B) := by
    change mixedMoment B node2661 node2661Labels = _
    exact sound2661 B hB hF
  have h2662 : mixedVector B (Sum.inr 2662) = Sparse.eval nodeValue2662 (mixedVector B) := by
    change mixedMoment B node2662 node2662Labels = _
    exact sound2662 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2708 : mixedVector B (Sum.inr 2708) = Sparse.eval nodeValue2708 (mixedVector B) := by
    change mixedMoment B node2708 node2708Labels = _
    exact sound2708 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h2718 : mixedVector B (Sum.inr 2718) = Sparse.eval nodeValue2718 (mixedVector B) := by
    change mixedMoment B node2718 node2718Labels = _
    exact sound2718 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h2753 : mixedVector B (Sum.inr 2753) = Sparse.eval nodeValue2753 (mixedVector B) := by
    change mixedMoment B node2753 node2753Labels = _
    exact sound2753 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h3979 : mixedVector B (Sum.inr 3979) = Sparse.eval nodeValue3979 (mixedVector B) := by
    change mixedMoment B node3979 node3979Labels = _
    exact sound3979 B hB hF
  have h3994 : mixedVector B (Sum.inr 3994) = Sparse.eval nodeValue3994 (mixedVector B) := by
    change mixedMoment B node3994 node3994Labels = _
    exact sound3994 B hB hF
  have h3998 : mixedVector B (Sum.inr 3998) = Sparse.eval nodeValue3998 (mixedVector B) := by
    change mixedMoment B node3998 node3998Labels = _
    exact sound3998 B hB hF
  simpa only [sourceForm802, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1017, h1018, h1021, h1032, h2566, h2567, h2570, h2587, h2661, h2662, h2669, h2708, h2710, h2718, h2751, h2753, h2763, h3849, h3979, h3994, h3998, reducedSource694] using sourceEq802 B hB

theorem rowSound694 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row694 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck694, numericCheck694, reducedZero694 B hB hF, mul_zero]

theorem reducedZero695 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource695 (mixedVector B) = 0 := by
  have h1635 : mixedVector B (Sum.inr 1635) = Sparse.eval nodeValue1635 (mixedVector B) := by
    change mixedMoment B node1635 node1635Labels = _
    exact sound1635 B hB hF
  have h1636 : mixedVector B (Sum.inr 1636) = Sparse.eval nodeValue1636 (mixedVector B) := by
    change mixedMoment B node1636 node1636Labels = _
    exact sound1636 B hB hF
  have h1642 : mixedVector B (Sum.inr 1642) = Sparse.eval nodeValue1642 (mixedVector B) := by
    change mixedMoment B node1642 node1642Labels = _
    exact sound1642 B hB hF
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h3375 : mixedVector B (Sum.inr 3375) = Sparse.eval nodeValue3375 (mixedVector B) := by
    change mixedMoment B node3375 node3375Labels = _
    exact sound3375 B hB hF
  have h3376 : mixedVector B (Sum.inr 3376) = Sparse.eval nodeValue3376 (mixedVector B) := by
    change mixedMoment B node3376 node3376Labels = _
    exact sound3376 B hB hF
  have h3388 : mixedVector B (Sum.inr 3388) = Sparse.eval nodeValue3388 (mixedVector B) := by
    change mixedMoment B node3388 node3388Labels = _
    exact sound3388 B hB hF
  have h3502 : mixedVector B (Sum.inr 3502) = Sparse.eval nodeValue3502 (mixedVector B) := by
    change mixedMoment B node3502 node3502Labels = _
    exact sound3502 B hB hF
  have h3503 : mixedVector B (Sum.inr 3503) = Sparse.eval nodeValue3503 (mixedVector B) := by
    change mixedMoment B node3503 node3503Labels = _
    exact sound3503 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3557 : mixedVector B (Sum.inr 3557) = Sparse.eval nodeValue3557 (mixedVector B) := by
    change mixedMoment B node3557 node3557Labels = _
    exact sound3557 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h3562 : mixedVector B (Sum.inr 3562) = Sparse.eval nodeValue3562 (mixedVector B) := by
    change mixedMoment B node3562 node3562Labels = _
    exact sound3562 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3605 : mixedVector B (Sum.inr 3605) = Sparse.eval nodeValue3605 (mixedVector B) := by
    change mixedMoment B node3605 node3605Labels = _
    exact sound3605 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  have h3984 : mixedVector B (Sum.inr 3984) = Sparse.eval nodeValue3984 (mixedVector B) := by
    change mixedMoment B node3984 node3984Labels = _
    exact sound3984 B hB hF
  have h3991 : mixedVector B (Sum.inr 3991) = Sparse.eval nodeValue3991 (mixedVector B) := by
    change mixedMoment B node3991 node3991Labels = _
    exact sound3991 B hB hF
  have h4026 : mixedVector B (Sum.inr 4026) = Sparse.eval nodeValue4026 (mixedVector B) := by
    change mixedMoment B node4026 node4026Labels = _
    exact sound4026 B hB hF
  simpa only [sourceForm803, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1635, h1636, h1642, h1713, h3375, h3376, h3388, h3502, h3503, h3539, h3557, h3558, h3562, h3572, h3580, h3605, h3625, h3974, h3984, h3991, h4026, reducedSource695] using sourceEq803 B hB

theorem rowSound695 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row695 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck695, numericCheck695, reducedZero695 B hB hF, mul_zero]

theorem reducedZero696 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource696 (mixedVector B) = 0 := by
  have h3074 : mixedVector B (Sum.inr 3074) = Sparse.eval nodeValue3074 (mixedVector B) := by
    change mixedMoment B node3074 node3074Labels = _
    exact sound3074 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  have h4008 : mixedVector B (Sum.inr 4008) = Sparse.eval nodeValue4008 (mixedVector B) := by
    change mixedMoment B node4008 node4008Labels = _
    exact sound4008 B hB hF
  have h4010 : mixedVector B (Sum.inr 4010) = Sparse.eval nodeValue4010 (mixedVector B) := by
    change mixedMoment B node4010 node4010Labels = _
    exact sound4010 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm804, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3074, h3875, h3974, h4008, h4010, h4091, reducedSource696] using sourceEq804 B hB

theorem rowSound696 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row696 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck696, numericCheck696, reducedZero696 B hB hF, mul_zero]

theorem reducedZero697 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource697 (mixedVector B) = 0 := by
  have h1383 : mixedVector B (Sum.inr 1383) = Sparse.eval nodeValue1383 (mixedVector B) := by
    change mixedMoment B node1383 node1383Labels = _
    exact sound1383 B hB hF
  have h1384 : mixedVector B (Sum.inr 1384) = Sparse.eval nodeValue1384 (mixedVector B) := by
    change mixedMoment B node1384 node1384Labels = _
    exact sound1384 B hB hF
  have h1387 : mixedVector B (Sum.inr 1387) = Sparse.eval nodeValue1387 (mixedVector B) := by
    change mixedMoment B node1387 node1387Labels = _
    exact sound1387 B hB hF
  have h1403 : mixedVector B (Sum.inr 1403) = Sparse.eval nodeValue1403 (mixedVector B) := by
    change mixedMoment B node1403 node1403Labels = _
    exact sound1403 B hB hF
  have h3074 : mixedVector B (Sum.inr 3074) = Sparse.eval nodeValue3074 (mixedVector B) := by
    change mixedMoment B node3074 node3074Labels = _
    exact sound3074 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm805, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1383, h1384, h1387, h1403, h3074, h4091, reducedSource697] using sourceEq805 B hB

theorem rowSound697 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row697 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck697, numericCheck697, reducedZero697 B hB hF, mul_zero]

theorem reducedZero698 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource698 (mixedVector B) = 0 := by
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h2925 : mixedVector B (Sum.inr 2925) = Sparse.eval nodeValue2925 (mixedVector B) := by
    change mixedMoment B node2925 node2925Labels = _
    exact sound2925 B hB hF
  have h2928 : mixedVector B (Sum.inr 2928) = Sparse.eval nodeValue2928 (mixedVector B) := by
    change mixedMoment B node2928 node2928Labels = _
    exact sound2928 B hB hF
  have h2951 : mixedVector B (Sum.inr 2951) = Sparse.eval nodeValue2951 (mixedVector B) := by
    change mixedMoment B node2951 node2951Labels = _
    exact sound2951 B hB hF
  have h3074 : mixedVector B (Sum.inr 3074) = Sparse.eval nodeValue3074 (mixedVector B) := by
    change mixedMoment B node3074 node3074Labels = _
    exact sound3074 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm806, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2924, h2925, h2928, h2951, h3074, h3974, h4091, reducedSource698] using sourceEq806 B hB

theorem rowSound698 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row698 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck698, numericCheck698, reducedZero698 B hB hF, mul_zero]

theorem reducedZero699 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource699 (mixedVector B) = 0 := by
  have h3068 : mixedVector B (Sum.inr 3068) = Sparse.eval nodeValue3068 (mixedVector B) := by
    change mixedMoment B node3068 node3068Labels = _
    exact sound3068 B hB hF
  have h3069 : mixedVector B (Sum.inr 3069) = Sparse.eval nodeValue3069 (mixedVector B) := by
    change mixedMoment B node3069 node3069Labels = _
    exact sound3069 B hB hF
  have h3074 : mixedVector B (Sum.inr 3074) = Sparse.eval nodeValue3074 (mixedVector B) := by
    change mixedMoment B node3074 node3074Labels = _
    exact sound3074 B hB hF
  have h3091 : mixedVector B (Sum.inr 3091) = Sparse.eval nodeValue3091 (mixedVector B) := by
    change mixedMoment B node3091 node3091Labels = _
    exact sound3091 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm807, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3068, h3069, h3074, h3091, h3875, h4091, reducedSource699] using sourceEq807 B hB

theorem rowSound699 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row699 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck699, numericCheck699, reducedZero699 B hB hF, mul_zero]

theorem reducedZero700 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource700 (mixedVector B) = 0 := by
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h2241 : mixedVector B (Sum.inr 2241) = Sparse.eval nodeValue2241 (mixedVector B) := by
    change mixedMoment B node2241 node2241Labels = _
    exact sound2241 B hB hF
  have h2243 : mixedVector B (Sum.inr 2243) = Sparse.eval nodeValue2243 (mixedVector B) := by
    change mixedMoment B node2243 node2243Labels = _
    exact sound2243 B hB hF
  have h2250 : mixedVector B (Sum.inr 2250) = Sparse.eval nodeValue2250 (mixedVector B) := by
    change mixedMoment B node2250 node2250Labels = _
    exact sound2250 B hB hF
  have h2565 : mixedVector B (Sum.inr 2565) = Sparse.eval nodeValue2565 (mixedVector B) := by
    change mixedMoment B node2565 node2565Labels = _
    exact sound2565 B hB hF
  have h2573 : mixedVector B (Sum.inr 2573) = Sparse.eval nodeValue2573 (mixedVector B) := by
    change mixedMoment B node2573 node2573Labels = _
    exact sound2573 B hB hF
  have h2583 : mixedVector B (Sum.inr 2583) = Sparse.eval nodeValue2583 (mixedVector B) := by
    change mixedMoment B node2583 node2583Labels = _
    exact sound2583 B hB hF
  have h2747 : mixedVector B (Sum.inr 2747) = Sparse.eval nodeValue2747 (mixedVector B) := by
    change mixedMoment B node2747 node2747Labels = _
    exact sound2747 B hB hF
  have h2749 : mixedVector B (Sum.inr 2749) = Sparse.eval nodeValue2749 (mixedVector B) := by
    change mixedMoment B node2749 node2749Labels = _
    exact sound2749 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h2752 : mixedVector B (Sum.inr 2752) = Sparse.eval nodeValue2752 (mixedVector B) := by
    change mixedMoment B node2752 node2752Labels = _
    exact sound2752 B hB hF
  have h2756 : mixedVector B (Sum.inr 2756) = Sparse.eval nodeValue2756 (mixedVector B) := by
    change mixedMoment B node2756 node2756Labels = _
    exact sound2756 B hB hF
  have h2757 : mixedVector B (Sum.inr 2757) = Sparse.eval nodeValue2757 (mixedVector B) := by
    change mixedMoment B node2757 node2757Labels = _
    exact sound2757 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h3104 : mixedVector B (Sum.inr 3104) = Sparse.eval nodeValue3104 (mixedVector B) := by
    change mixedMoment B node3104 node3104Labels = _
    exact sound3104 B hB hF
  have h3105 : mixedVector B (Sum.inr 3105) = Sparse.eval nodeValue3105 (mixedVector B) := by
    change mixedMoment B node3105 node3105Labels = _
    exact sound3105 B hB hF
  have h3109 : mixedVector B (Sum.inr 3109) = Sparse.eval nodeValue3109 (mixedVector B) := by
    change mixedMoment B node3109 node3109Labels = _
    exact sound3109 B hB hF
  simpa only [sourceForm809, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2240, h2241, h2243, h2250, h2565, h2573, h2583, h2747, h2749, h2750, h2752, h2756, h2757, h2763, h2764, h2766, h2773, h3104, h3105, h3109, reducedSource700] using sourceEq809 B hB

theorem rowSound700 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row700 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck700, numericCheck700, reducedZero700 B hB hF, mul_zero]

theorem reducedZero701 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource701 (mixedVector B) = 0 := by
  have h2923 : mixedVector B (Sum.inr 2923) = Sparse.eval nodeValue2923 (mixedVector B) := by
    change mixedMoment B node2923 node2923Labels = _
    exact sound2923 B hB hF
  have h3489 : mixedVector B (Sum.inr 3489) = Sparse.eval nodeValue3489 (mixedVector B) := by
    change mixedMoment B node3489 node3489Labels = _
    exact sound3489 B hB hF
  have h3496 : mixedVector B (Sum.inr 3496) = Sparse.eval nodeValue3496 (mixedVector B) := by
    change mixedMoment B node3496 node3496Labels = _
    exact sound3496 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm811, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2923, h3489, h3496, h3534, h3571, h4083, reducedSource701] using sourceEq811 B hB

theorem rowSound701 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row701 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck701, numericCheck701, reducedZero701 B hB hF, mul_zero]

theorem reducedZero702 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource702 (mixedVector B) = 0 := by
  have h2088 : mixedVector B (Sum.inr 2088) = Sparse.eval nodeValue2088 (mixedVector B) := by
    change mixedMoment B node2088 node2088Labels = _
    exact sound2088 B hB hF
  have h2089 : mixedVector B (Sum.inr 2089) = Sparse.eval nodeValue2089 (mixedVector B) := by
    change mixedMoment B node2089 node2089Labels = _
    exact sound2089 B hB hF
  have h2105 : mixedVector B (Sum.inr 2105) = Sparse.eval nodeValue2105 (mixedVector B) := by
    change mixedMoment B node2105 node2105Labels = _
    exact sound2105 B hB hF
  have h2243 : mixedVector B (Sum.inr 2243) = Sparse.eval nodeValue2243 (mixedVector B) := by
    change mixedMoment B node2243 node2243Labels = _
    exact sound2243 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm812, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2088, h2089, h2105, h2243, h3571, h4083, reducedSource702] using sourceEq812 B hB

theorem rowSound702 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row702 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck702, numericCheck702, reducedZero702 B hB hF, mul_zero]

theorem reducedZero703 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource703 (mixedVector B) = 0 := by
  have h2923 : mixedVector B (Sum.inr 2923) = Sparse.eval nodeValue2923 (mixedVector B) := by
    change mixedMoment B node2923 node2923Labels = _
    exact sound2923 B hB hF
  have h2926 : mixedVector B (Sum.inr 2926) = Sparse.eval nodeValue2926 (mixedVector B) := by
    change mixedMoment B node2926 node2926Labels = _
    exact sound2926 B hB hF
  have h2950 : mixedVector B (Sum.inr 2950) = Sparse.eval nodeValue2950 (mixedVector B) := by
    change mixedMoment B node2950 node2950Labels = _
    exact sound2950 B hB hF
  have h3073 : mixedVector B (Sum.inr 3073) = Sparse.eval nodeValue3073 (mixedVector B) := by
    change mixedMoment B node3073 node3073Labels = _
    exact sound3073 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm813, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2923, h2926, h2950, h3073, h3571, h4083, reducedSource703] using sourceEq813 B hB

theorem rowSound703 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row703 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck703, numericCheck703, reducedZero703 B hB hF, mul_zero]

theorem sourceRowsAt688 : MixedData.sourceRows (688 : Fin 2425) =
    MixedData.row688 := by decide +kernel

theorem sourceRowsAt689 : MixedData.sourceRows (689 : Fin 2425) =
    MixedData.row689 := by decide +kernel

theorem sourceRowsAt690 : MixedData.sourceRows (690 : Fin 2425) =
    MixedData.row690 := by decide +kernel

theorem sourceRowsAt691 : MixedData.sourceRows (691 : Fin 2425) =
    MixedData.row691 := by decide +kernel

theorem sourceRowsAt692 : MixedData.sourceRows (692 : Fin 2425) =
    MixedData.row692 := by decide +kernel

theorem sourceRowsAt693 : MixedData.sourceRows (693 : Fin 2425) =
    MixedData.row693 := by decide +kernel

theorem sourceRowsAt694 : MixedData.sourceRows (694 : Fin 2425) =
    MixedData.row694 := by decide +kernel

theorem sourceRowsAt695 : MixedData.sourceRows (695 : Fin 2425) =
    MixedData.row695 := by decide +kernel

theorem sourceRowsAt696 : MixedData.sourceRows (696 : Fin 2425) =
    MixedData.row696 := by decide +kernel

theorem sourceRowsAt697 : MixedData.sourceRows (697 : Fin 2425) =
    MixedData.row697 := by decide +kernel

theorem sourceRowsAt698 : MixedData.sourceRows (698 : Fin 2425) =
    MixedData.row698 := by decide +kernel

theorem sourceRowsAt699 : MixedData.sourceRows (699 : Fin 2425) =
    MixedData.row699 := by decide +kernel

theorem sourceRowsAt700 : MixedData.sourceRows (700 : Fin 2425) =
    MixedData.row700 := by decide +kernel

theorem sourceRowsAt701 : MixedData.sourceRows (701 : Fin 2425) =
    MixedData.row701 := by decide +kernel

theorem sourceRowsAt702 : MixedData.sourceRows (702 : Fin 2425) =
    MixedData.row702 := by decide +kernel

theorem sourceRowsAt703 : MixedData.sourceRows (703 : Fin 2425) =
    MixedData.row703 := by decide +kernel

theorem chunkSound43 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 43) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 688 ∨ k.val = 689 ∨ k.val = 690 ∨ k.val = 691 ∨ k.val = 692 ∨ k.val = 693 ∨ k.val = 694 ∨ k.val = 695 ∨ k.val = 696 ∨ k.val = 697 ∨ k.val = 698 ∨ k.val = 699 ∨ k.val = 700 ∨ k.val = 701 ∨ k.val = 702 ∨ k.val = 703 := by omega
  rcases heq with h688 | h689 | h690 | h691 | h692 | h693 | h694 | h695 | h696 | h697 | h698 | h699 | h700 | h701 | h702 | h703
  · have he : k = (688 : Fin 2425) := Fin.ext h688
    subst k
    rw [sourceRowsAt688]
    exact rowSound688 B hB hF
  · have he : k = (689 : Fin 2425) := Fin.ext h689
    subst k
    rw [sourceRowsAt689]
    exact rowSound689 B hB hF
  · have he : k = (690 : Fin 2425) := Fin.ext h690
    subst k
    rw [sourceRowsAt690]
    exact rowSound690 B hB hF
  · have he : k = (691 : Fin 2425) := Fin.ext h691
    subst k
    rw [sourceRowsAt691]
    exact rowSound691 B hB hF
  · have he : k = (692 : Fin 2425) := Fin.ext h692
    subst k
    rw [sourceRowsAt692]
    exact rowSound692 B hB hF
  · have he : k = (693 : Fin 2425) := Fin.ext h693
    subst k
    rw [sourceRowsAt693]
    exact rowSound693 B hB hF
  · have he : k = (694 : Fin 2425) := Fin.ext h694
    subst k
    rw [sourceRowsAt694]
    exact rowSound694 B hB hF
  · have he : k = (695 : Fin 2425) := Fin.ext h695
    subst k
    rw [sourceRowsAt695]
    exact rowSound695 B hB hF
  · have he : k = (696 : Fin 2425) := Fin.ext h696
    subst k
    rw [sourceRowsAt696]
    exact rowSound696 B hB hF
  · have he : k = (697 : Fin 2425) := Fin.ext h697
    subst k
    rw [sourceRowsAt697]
    exact rowSound697 B hB hF
  · have he : k = (698 : Fin 2425) := Fin.ext h698
    subst k
    rw [sourceRowsAt698]
    exact rowSound698 B hB hF
  · have he : k = (699 : Fin 2425) := Fin.ext h699
    subst k
    rw [sourceRowsAt699]
    exact rowSound699 B hB hF
  · have he : k = (700 : Fin 2425) := Fin.ext h700
    subst k
    rw [sourceRowsAt700]
    exact rowSound700 B hB hF
  · have he : k = (701 : Fin 2425) := Fin.ext h701
    subst k
    rw [sourceRowsAt701]
    exact rowSound701 B hB hF
  · have he : k = (702 : Fin 2425) := Fin.ext h702
    subst k
    rw [sourceRowsAt702]
    exact rowSound702 B hB hF
  · have he : k = (703 : Fin 2425) := Fin.ext h703
    subst k
    rw [sourceRowsAt703]
    exact rowSound703 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
