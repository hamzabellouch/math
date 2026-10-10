import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources23

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero640 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource640 (mixedVector B) = 0 := by
  have h1291 : mixedVector B (Sum.inr 1291) = Sparse.eval nodeValue1291 (mixedVector B) := by
    change mixedMoment B node1291 node1291Labels = _
    exact sound1291 B hB hF
  have h2587 : mixedVector B (Sum.inr 2587) = Sparse.eval nodeValue2587 (mixedVector B) := by
    change mixedMoment B node2587 node2587Labels = _
    exact sound2587 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm736, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1291, h2587, h2739, h2763, h2773, h2782, h4092, reducedSource640] using sourceEq736 B hB

theorem rowSound640 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row640 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck640, numericCheck640, reducedZero640 B hB hF, mul_zero]

theorem reducedZero641 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource641 (mixedVector B) = 0 := by
  have h2630 : mixedVector B (Sum.inr 2630) = Sparse.eval nodeValue2630 (mixedVector B) := by
    change mixedMoment B node2630 node2630Labels = _
    exact sound2630 B hB hF
  have h2632 : mixedVector B (Sum.inr 2632) = Sparse.eval nodeValue2632 (mixedVector B) := by
    change mixedMoment B node2632 node2632Labels = _
    exact sound2632 B hB hF
  have h2634 : mixedVector B (Sum.inr 2634) = Sparse.eval nodeValue2634 (mixedVector B) := by
    change mixedMoment B node2634 node2634Labels = _
    exact sound2634 B hB hF
  have h2639 : mixedVector B (Sum.inr 2639) = Sparse.eval nodeValue2639 (mixedVector B) := by
    change mixedMoment B node2639 node2639Labels = _
    exact sound2639 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm737, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2630, h2632, h2634, h2639, h2763, h3884, h4092, reducedSource641] using sourceEq737 B hB

theorem rowSound641 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row641 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck641, numericCheck641, reducedZero641 B hB hF, mul_zero]

theorem reducedZero642 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource642 (mixedVector B) = 0 := by
  have h4449 : mixedVector B (Sum.inr 4449) = Sparse.eval nodeValue4449 (mixedVector B) := by
    change mixedMoment B node4449 node4449Labels = _
    exact sound4449 B hB hF
  have h4450 : mixedVector B (Sum.inr 4450) = Sparse.eval nodeValue4450 (mixedVector B) := by
    change mixedMoment B node4450 node4450Labels = _
    exact sound4450 B hB hF
  have h4453 : mixedVector B (Sum.inr 4453) = Sparse.eval nodeValue4453 (mixedVector B) := by
    change mixedMoment B node4453 node4453Labels = _
    exact sound4453 B hB hF
  have h4459 : mixedVector B (Sum.inr 4459) = Sparse.eval nodeValue4459 (mixedVector B) := by
    change mixedMoment B node4459 node4459Labels = _
    exact sound4459 B hB hF
  have h4487 : mixedVector B (Sum.inr 4487) = Sparse.eval nodeValue4487 (mixedVector B) := by
    change mixedMoment B node4487 node4487Labels = _
    exact sound4487 B hB hF
  have h5069 : mixedVector B (Sum.inr 5069) = Sparse.eval nodeValue5069 (mixedVector B) := by
    change mixedMoment B node5069 node5069Labels = _
    exact sound5069 B hB hF
  have h5071 : mixedVector B (Sum.inr 5071) = Sparse.eval nodeValue5071 (mixedVector B) := by
    change mixedMoment B node5071 node5071Labels = _
    exact sound5071 B hB hF
  have h5074 : mixedVector B (Sum.inr 5074) = Sparse.eval nodeValue5074 (mixedVector B) := by
    change mixedMoment B node5074 node5074Labels = _
    exact sound5074 B hB hF
  have h5092 : mixedVector B (Sum.inr 5092) = Sparse.eval nodeValue5092 (mixedVector B) := by
    change mixedMoment B node5092 node5092Labels = _
    exact sound5092 B hB hF
  have h5140 : mixedVector B (Sum.inr 5140) = Sparse.eval nodeValue5140 (mixedVector B) := by
    change mixedMoment B node5140 node5140Labels = _
    exact sound5140 B hB hF
  have h5160 : mixedVector B (Sum.inr 5160) = Sparse.eval nodeValue5160 (mixedVector B) := by
    change mixedMoment B node5160 node5160Labels = _
    exact sound5160 B hB hF
  have h5161 : mixedVector B (Sum.inr 5161) = Sparse.eval nodeValue5161 (mixedVector B) := by
    change mixedMoment B node5161 node5161Labels = _
    exact sound5161 B hB hF
  have h5164 : mixedVector B (Sum.inr 5164) = Sparse.eval nodeValue5164 (mixedVector B) := by
    change mixedMoment B node5164 node5164Labels = _
    exact sound5164 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5226 : mixedVector B (Sum.inr 5226) = Sparse.eval nodeValue5226 (mixedVector B) := by
    change mixedMoment B node5226 node5226Labels = _
    exact sound5226 B hB hF
  have h5229 : mixedVector B (Sum.inr 5229) = Sparse.eval nodeValue5229 (mixedVector B) := by
    change mixedMoment B node5229 node5229Labels = _
    exact sound5229 B hB hF
  have h5236 : mixedVector B (Sum.inr 5236) = Sparse.eval nodeValue5236 (mixedVector B) := by
    change mixedMoment B node5236 node5236Labels = _
    exact sound5236 B hB hF
  have h5255 : mixedVector B (Sum.inr 5255) = Sparse.eval nodeValue5255 (mixedVector B) := by
    change mixedMoment B node5255 node5255Labels = _
    exact sound5255 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5269 : mixedVector B (Sum.inr 5269) = Sparse.eval nodeValue5269 (mixedVector B) := by
    change mixedMoment B node5269 node5269Labels = _
    exact sound5269 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5289 : mixedVector B (Sum.inr 5289) = Sparse.eval nodeValue5289 (mixedVector B) := by
    change mixedMoment B node5289 node5289Labels = _
    exact sound5289 B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5480 : mixedVector B (Sum.inr 5480) = Sparse.eval nodeValue5480 (mixedVector B) := by
    change mixedMoment B node5480 node5480Labels = _
    exact sound5480 B hB hF
  have h5484 : mixedVector B (Sum.inr 5484) = Sparse.eval nodeValue5484 (mixedVector B) := by
    change mixedMoment B node5484 node5484Labels = _
    exact sound5484 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485 B hB hF
  simpa only [sourceForm738, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4449, h4450, h4453, h4459, h4487, h5069, h5071, h5074, h5092, h5140, h5160, h5161, h5164, h5170, h5226, h5229, h5236, h5255, h5260, h5269, h5281, h5282, h5284, h5289, h5438, h5480, h5484, h5485, reducedSource642] using sourceEq738 B hB

theorem rowSound642 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row642 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck642, numericCheck642, reducedZero642 B hB hF, mul_zero]

theorem reducedZero643 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource643 (mixedVector B) = 0 := by
  have h1032 : mixedVector B (Sum.inr 1032) = Sparse.eval nodeValue1032 (mixedVector B) := by
    change mixedMoment B node1032 node1032Labels = _
    exact sound1032 B hB hF
  have h1033 : mixedVector B (Sum.inr 1033) = Sparse.eval nodeValue1033 (mixedVector B) := by
    change mixedMoment B node1033 node1033Labels = _
    exact sound1033 B hB hF
  have h1036 : mixedVector B (Sum.inr 1036) = Sparse.eval nodeValue1036 (mixedVector B) := by
    change mixedMoment B node1036 node1036Labels = _
    exact sound1036 B hB hF
  have h1042 : mixedVector B (Sum.inr 1042) = Sparse.eval nodeValue1042 (mixedVector B) := by
    change mixedMoment B node1042 node1042Labels = _
    exact sound1042 B hB hF
  have h1071 : mixedVector B (Sum.inr 1071) = Sparse.eval nodeValue1071 (mixedVector B) := by
    change mixedMoment B node1071 node1071Labels = _
    exact sound1071 B hB hF
  have h2476 : mixedVector B (Sum.inr 2476) = Sparse.eval nodeValue2476 (mixedVector B) := by
    change mixedMoment B node2476 node2476Labels = _
    exact sound2476 B hB hF
  have h2478 : mixedVector B (Sum.inr 2478) = Sparse.eval nodeValue2478 (mixedVector B) := by
    change mixedMoment B node2478 node2478Labels = _
    exact sound2478 B hB hF
  have h2481 : mixedVector B (Sum.inr 2481) = Sparse.eval nodeValue2481 (mixedVector B) := by
    change mixedMoment B node2481 node2481Labels = _
    exact sound2481 B hB hF
  have h2501 : mixedVector B (Sum.inr 2501) = Sparse.eval nodeValue2501 (mixedVector B) := by
    change mixedMoment B node2501 node2501Labels = _
    exact sound2501 B hB hF
  have h2587 : mixedVector B (Sum.inr 2587) = Sparse.eval nodeValue2587 (mixedVector B) := by
    change mixedMoment B node2587 node2587Labels = _
    exact sound2587 B hB hF
  have h2588 : mixedVector B (Sum.inr 2588) = Sparse.eval nodeValue2588 (mixedVector B) := by
    change mixedMoment B node2588 node2588Labels = _
    exact sound2588 B hB hF
  have h2591 : mixedVector B (Sum.inr 2591) = Sparse.eval nodeValue2591 (mixedVector B) := by
    change mixedMoment B node2591 node2591Labels = _
    exact sound2591 B hB hF
  have h2596 : mixedVector B (Sum.inr 2596) = Sparse.eval nodeValue2596 (mixedVector B) := by
    change mixedMoment B node2596 node2596Labels = _
    exact sound2596 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h2673 : mixedVector B (Sum.inr 2673) = Sparse.eval nodeValue2673 (mixedVector B) := by
    change mixedMoment B node2673 node2673Labels = _
    exact sound2673 B hB hF
  have h2682 : mixedVector B (Sum.inr 2682) = Sparse.eval nodeValue2682 (mixedVector B) := by
    change mixedMoment B node2682 node2682Labels = _
    exact sound2682 B hB hF
  have h2718 : mixedVector B (Sum.inr 2718) = Sparse.eval nodeValue2718 (mixedVector B) := by
    change mixedMoment B node2718 node2718Labels = _
    exact sound2718 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h2736 : mixedVector B (Sum.inr 2736) = Sparse.eval nodeValue2736 (mixedVector B) := by
    change mixedMoment B node2736 node2736Labels = _
    exact sound2736 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h2753 : mixedVector B (Sum.inr 2753) = Sparse.eval nodeValue2753 (mixedVector B) := by
    change mixedMoment B node2753 node2753Labels = _
    exact sound2753 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3978 : mixedVector B (Sum.inr 3978) = Sparse.eval nodeValue3978 (mixedVector B) := by
    change mixedMoment B node3978 node3978Labels = _
    exact sound3978 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  have h3997 : mixedVector B (Sum.inr 3997) = Sparse.eval nodeValue3997 (mixedVector B) := by
    change mixedMoment B node3997 node3997Labels = _
    exact sound3997 B hB hF
  have h3998 : mixedVector B (Sum.inr 3998) = Sparse.eval nodeValue3998 (mixedVector B) := by
    change mixedMoment B node3998 node3998Labels = _
    exact sound3998 B hB hF
  simpa only [sourceForm739, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1032, h1033, h1036, h1042, h1071, h2476, h2478, h2481, h2501, h2587, h2588, h2591, h2596, h2669, h2670, h2673, h2682, h2718, h2719, h2724, h2736, h2750, h2751, h2753, h2763, h3857, h3978, h3983, h3997, h3998, reducedSource643] using sourceEq739 B hB

theorem rowSound643 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row643 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck643, numericCheck643, reducedZero643 B hB hF, mul_zero]

theorem reducedZero644 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource644 (mixedVector B) = 0 := by
  have h1636 : mixedVector B (Sum.inr 1636) = Sparse.eval nodeValue1636 (mixedVector B) := by
    change mixedMoment B node1636 node1636Labels = _
    exact sound1636 B hB hF
  have h1637 : mixedVector B (Sum.inr 1637) = Sparse.eval nodeValue1637 (mixedVector B) := by
    change mixedMoment B node1637 node1637Labels = _
    exact sound1637 B hB hF
  have h1641 : mixedVector B (Sum.inr 1641) = Sparse.eval nodeValue1641 (mixedVector B) := by
    change mixedMoment B node1641 node1641Labels = _
    exact sound1641 B hB hF
  have h1646 : mixedVector B (Sum.inr 1646) = Sparse.eval nodeValue1646 (mixedVector B) := by
    change mixedMoment B node1646 node1646Labels = _
    exact sound1646 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h2550 : mixedVector B (Sum.inr 2550) = Sparse.eval nodeValue2550 (mixedVector B) := by
    change mixedMoment B node2550 node2550Labels = _
    exact sound2550 B hB hF
  have h2560 : mixedVector B (Sum.inr 2560) = Sparse.eval nodeValue2560 (mixedVector B) := by
    change mixedMoment B node2560 node2560Labels = _
    exact sound2560 B hB hF
  have h2588 : mixedVector B (Sum.inr 2588) = Sparse.eval nodeValue2588 (mixedVector B) := by
    change mixedMoment B node2588 node2588Labels = _
    exact sound2588 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h3376 : mixedVector B (Sum.inr 3376) = Sparse.eval nodeValue3376 (mixedVector B) := by
    change mixedMoment B node3376 node3376Labels = _
    exact sound3376 B hB hF
  have h3380 : mixedVector B (Sum.inr 3380) = Sparse.eval nodeValue3380 (mixedVector B) := by
    change mixedMoment B node3380 node3380Labels = _
    exact sound3380 B hB hF
  have h3392 : mixedVector B (Sum.inr 3392) = Sparse.eval nodeValue3392 (mixedVector B) := by
    change mixedMoment B node3392 node3392Labels = _
    exact sound3392 B hB hF
  have h3442 : mixedVector B (Sum.inr 3442) = Sparse.eval nodeValue3442 (mixedVector B) := by
    change mixedMoment B node3442 node3442Labels = _
    exact sound3442 B hB hF
  have h3445 : mixedVector B (Sum.inr 3445) = Sparse.eval nodeValue3445 (mixedVector B) := by
    change mixedMoment B node3445 node3445Labels = _
    exact sound3445 B hB hF
  have h3463 : mixedVector B (Sum.inr 3463) = Sparse.eval nodeValue3463 (mixedVector B) := by
    change mixedMoment B node3463 node3463Labels = _
    exact sound3463 B hB hF
  have h3503 : mixedVector B (Sum.inr 3503) = Sparse.eval nodeValue3503 (mixedVector B) := by
    change mixedMoment B node3503 node3503Labels = _
    exact sound3503 B hB hF
  have h3507 : mixedVector B (Sum.inr 3507) = Sparse.eval nodeValue3507 (mixedVector B) := by
    change mixedMoment B node3507 node3507Labels = _
    exact sound3507 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h3565 : mixedVector B (Sum.inr 3565) = Sparse.eval nodeValue3565 (mixedVector B) := by
    change mixedMoment B node3565 node3565Labels = _
    exact sound3565 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3606 : mixedVector B (Sum.inr 3606) = Sparse.eval nodeValue3606 (mixedVector B) := by
    change mixedMoment B node3606 node3606Labels = _
    exact sound3606 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3978 : mixedVector B (Sum.inr 3978) = Sparse.eval nodeValue3978 (mixedVector B) := by
    change mixedMoment B node3978 node3978Labels = _
    exact sound3978 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  have h3984 : mixedVector B (Sum.inr 3984) = Sparse.eval nodeValue3984 (mixedVector B) := by
    change mixedMoment B node3984 node3984Labels = _
    exact sound3984 B hB hF
  have h3993 : mixedVector B (Sum.inr 3993) = Sparse.eval nodeValue3993 (mixedVector B) := by
    change mixedMoment B node3993 node3993Labels = _
    exact sound3993 B hB hF
  have h3997 : mixedVector B (Sum.inr 3997) = Sparse.eval nodeValue3997 (mixedVector B) := by
    change mixedMoment B node3997 node3997Labels = _
    exact sound3997 B hB hF
  simpa only [sourceForm740, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1636, h1637, h1641, h1646, h1714, h2550, h2560, h2588, h2719, h3376, h3380, h3392, h3442, h3445, h3463, h3503, h3507, h3540, h3558, h3565, h3571, h3572, h3580, h3606, h3625, h3978, h3983, h3984, h3993, h3997, reducedSource644] using sourceEq740 B hB

theorem rowSound644 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row644 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck644, numericCheck644, reducedZero644 B hB hF, mul_zero]

theorem reducedZero645 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource645 (mixedVector B) = 0 := by
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3978 : mixedVector B (Sum.inr 3978) = Sparse.eval nodeValue3978 (mixedVector B) := by
    change mixedMoment B node3978 node3978Labels = _
    exact sound3978 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  have h4010 : mixedVector B (Sum.inr 4010) = Sparse.eval nodeValue4010 (mixedVector B) := by
    change mixedMoment B node4010 node4010Labels = _
    exact sound4010 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm741, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3097, h3876, h3978, h3983, h4010, h4091, reducedSource645] using sourceEq741 B hB

theorem rowSound645 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row645 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck645, numericCheck645, reducedZero645 B hB hF, mul_zero]

theorem reducedZero646 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource646 (mixedVector B) = 0 := by
  have h1403 : mixedVector B (Sum.inr 1403) = Sparse.eval nodeValue1403 (mixedVector B) := by
    change mixedMoment B node1403 node1403Labels = _
    exact sound1403 B hB hF
  have h2951 : mixedVector B (Sum.inr 2951) = Sparse.eval nodeValue2951 (mixedVector B) := by
    change mixedMoment B node2951 node2951Labels = _
    exact sound2951 B hB hF
  have h3074 : mixedVector B (Sum.inr 3074) = Sparse.eval nodeValue3074 (mixedVector B) := by
    change mixedMoment B node3074 node3074Labels = _
    exact sound3074 B hB hF
  have h3084 : mixedVector B (Sum.inr 3084) = Sparse.eval nodeValue3084 (mixedVector B) := by
    change mixedMoment B node3084 node3084Labels = _
    exact sound3084 B hB hF
  have h3091 : mixedVector B (Sum.inr 3091) = Sparse.eval nodeValue3091 (mixedVector B) := by
    change mixedMoment B node3091 node3091Labels = _
    exact sound3091 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm743, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1403, h2951, h3074, h3084, h3091, h3097, h4091, reducedSource646] using sourceEq743 B hB

theorem rowSound646 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row646 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck646, numericCheck646, reducedZero646 B hB hF, mul_zero]

theorem reducedZero647 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource647 (mixedVector B) = 0 := by
  have h2951 : mixedVector B (Sum.inr 2951) = Sparse.eval nodeValue2951 (mixedVector B) := by
    change mixedMoment B node2951 node2951Labels = _
    exact sound2951 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h2955 : mixedVector B (Sum.inr 2955) = Sparse.eval nodeValue2955 (mixedVector B) := by
    change mixedMoment B node2955 node2955Labels = _
    exact sound2955 B hB hF
  have h2964 : mixedVector B (Sum.inr 2964) = Sparse.eval nodeValue2964 (mixedVector B) := by
    change mixedMoment B node2964 node2964Labels = _
    exact sound2964 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm746, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2951, h2954, h2955, h2964, h3097, h3983, h4091, reducedSource647] using sourceEq746 B hB

theorem rowSound647 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row647 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck647, numericCheck647, reducedZero647 B hB hF, mul_zero]

theorem reducedZero648 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource648 (mixedVector B) = 0 := by
  have h2942 : mixedVector B (Sum.inr 2942) = Sparse.eval nodeValue2942 (mixedVector B) := by
    change mixedMoment B node2942 node2942Labels = _
    exact sound2942 B hB hF
  have h3091 : mixedVector B (Sum.inr 3091) = Sparse.eval nodeValue3091 (mixedVector B) := by
    change mixedMoment B node3091 node3091Labels = _
    exact sound3091 B hB hF
  have h3092 : mixedVector B (Sum.inr 3092) = Sparse.eval nodeValue3092 (mixedVector B) := by
    change mixedMoment B node3092 node3092Labels = _
    exact sound3092 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h3115 : mixedVector B (Sum.inr 3115) = Sparse.eval nodeValue3115 (mixedVector B) := by
    change mixedMoment B node3115 node3115Labels = _
    exact sound3115 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm747, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2942, h3091, h3092, h3097, h3115, h3876, h4091, reducedSource648] using sourceEq747 B hB

theorem rowSound648 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row648 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck648, numericCheck648, reducedZero648 B hB hF, mul_zero]

theorem reducedZero649 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource649 (mixedVector B) = 0 := by
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h2583 : mixedVector B (Sum.inr 2583) = Sparse.eval nodeValue2583 (mixedVector B) := by
    change mixedMoment B node2583 node2583Labels = _
    exact sound2583 B hB hF
  have h2584 : mixedVector B (Sum.inr 2584) = Sparse.eval nodeValue2584 (mixedVector B) := by
    change mixedMoment B node2584 node2584Labels = _
    exact sound2584 B hB hF
  have h2585 : mixedVector B (Sum.inr 2585) = Sparse.eval nodeValue2585 (mixedVector B) := by
    change mixedMoment B node2585 node2585Labels = _
    exact sound2585 B hB hF
  have h2600 : mixedVector B (Sum.inr 2600) = Sparse.eval nodeValue2600 (mixedVector B) := by
    change mixedMoment B node2600 node2600Labels = _
    exact sound2600 B hB hF
  have h2717 : mixedVector B (Sum.inr 2717) = Sparse.eval nodeValue2717 (mixedVector B) := by
    change mixedMoment B node2717 node2717Labels = _
    exact sound2717 B hB hF
  have h2718 : mixedVector B (Sum.inr 2718) = Sparse.eval nodeValue2718 (mixedVector B) := by
    change mixedMoment B node2718 node2718Labels = _
    exact sound2718 B hB hF
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h2727 : mixedVector B (Sum.inr 2727) = Sparse.eval nodeValue2727 (mixedVector B) := by
    change mixedMoment B node2727 node2727Labels = _
    exact sound2727 B hB hF
  have h2749 : mixedVector B (Sum.inr 2749) = Sparse.eval nodeValue2749 (mixedVector B) := by
    change mixedMoment B node2749 node2749Labels = _
    exact sound2749 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h2760 : mixedVector B (Sum.inr 2760) = Sparse.eval nodeValue2760 (mixedVector B) := by
    change mixedMoment B node2760 node2760Labels = _
    exact sound2760 B hB hF
  have h2762 : mixedVector B (Sum.inr 2762) = Sparse.eval nodeValue2762 (mixedVector B) := by
    change mixedMoment B node2762 node2762Labels = _
    exact sound2762 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766 B hB hF
  have h2772 : mixedVector B (Sum.inr 2772) = Sparse.eval nodeValue2772 (mixedVector B) := by
    change mixedMoment B node2772 node2772Labels = _
    exact sound2772 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  have h2784 : mixedVector B (Sum.inr 2784) = Sparse.eval nodeValue2784 (mixedVector B) := by
    change mixedMoment B node2784 node2784Labels = _
    exact sound2784 B hB hF
  have h3084 : mixedVector B (Sum.inr 3084) = Sparse.eval nodeValue3084 (mixedVector B) := by
    change mixedMoment B node3084 node3084Labels = _
    exact sound3084 B hB hF
  have h3108 : mixedVector B (Sum.inr 3108) = Sparse.eval nodeValue3108 (mixedVector B) := by
    change mixedMoment B node3108 node3108Labels = _
    exact sound3108 B hB hF
  have h3109 : mixedVector B (Sum.inr 3109) = Sparse.eval nodeValue3109 (mixedVector B) := by
    change mixedMoment B node3109 node3109Labels = _
    exact sound3109 B hB hF
  have h3119 : mixedVector B (Sum.inr 3119) = Sparse.eval nodeValue3119 (mixedVector B) := by
    change mixedMoment B node3119 node3119Labels = _
    exact sound3119 B hB hF
  simpa only [sourceForm749, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2240, h2259, h2260, h2262, h2274, h2583, h2584, h2585, h2600, h2717, h2718, h2720, h2727, h2749, h2750, h2760, h2762, h2763, h2764, h2766, h2772, h2773, h2781, h2782, h2784, h3084, h3108, h3109, h3119, reducedSource649] using sourceEq749 B hB

theorem rowSound649 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row649 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck649, numericCheck649, reducedZero649 B hB hF, mul_zero]

theorem reducedZero650 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource650 (mixedVector B) = 0 := by
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h3503 : mixedVector B (Sum.inr 3503) = Sparse.eval nodeValue3503 (mixedVector B) := by
    change mixedMoment B node3503 node3503Labels = _
    exact sound3503 B hB hF
  have h3507 : mixedVector B (Sum.inr 3507) = Sparse.eval nodeValue3507 (mixedVector B) := by
    change mixedMoment B node3507 node3507Labels = _
    exact sound3507 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm751, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2952, h3503, h3507, h3534, h3572, h3583, h4083, reducedSource650] using sourceEq751 B hB

theorem rowSound650 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row650 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck650, numericCheck650, reducedZero650 B hB hF, mul_zero]

theorem reducedZero651 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource651 (mixedVector B) = 0 := by
  have h2088 : mixedVector B (Sum.inr 2088) = Sparse.eval nodeValue2088 (mixedVector B) := by
    change mixedMoment B node2088 node2088Labels = _
    exact sound2088 B hB hF
  have h2950 : mixedVector B (Sum.inr 2950) = Sparse.eval nodeValue2950 (mixedVector B) := by
    change mixedMoment B node2950 node2950Labels = _
    exact sound2950 B hB hF
  have h3550 : mixedVector B (Sum.inr 3550) = Sparse.eval nodeValue3550 (mixedVector B) := by
    change mixedMoment B node3550 node3550Labels = _
    exact sound3550 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm752, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2088, h2950, h3550, h3571, h3572, h4083, reducedSource651] using sourceEq752 B hB

theorem rowSound651 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row651 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck651, numericCheck651, reducedZero651 B hB hF, mul_zero]

theorem reducedZero652 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource652 (mixedVector B) = 0 := by
  have h2094 : mixedVector B (Sum.inr 2094) = Sparse.eval nodeValue2094 (mixedVector B) := by
    change mixedMoment B node2094 node2094Labels = _
    exact sound2094 B hB hF
  have h2956 : mixedVector B (Sum.inr 2956) = Sparse.eval nodeValue2956 (mixedVector B) := by
    change mixedMoment B node2956 node2956Labels = _
    exact sound2956 B hB hF
  have h3500 : mixedVector B (Sum.inr 3500) = Sparse.eval nodeValue3500 (mixedVector B) := by
    change mixedMoment B node3500 node3500Labels = _
    exact sound3500 B hB hF
  have h3552 : mixedVector B (Sum.inr 3552) = Sparse.eval nodeValue3552 (mixedVector B) := by
    change mixedMoment B node3552 node3552Labels = _
    exact sound3552 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm753, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2094, h2956, h3500, h3552, h3572, h3573, h4083, reducedSource652] using sourceEq753 B hB

theorem rowSound652 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row652 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck652, numericCheck652, reducedZero652 B hB hF, mul_zero]

theorem reducedZero653 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource653 (mixedVector B) = 0 := by
  have h2950 : mixedVector B (Sum.inr 2950) = Sparse.eval nodeValue2950 (mixedVector B) := by
    change mixedMoment B node2950 node2950Labels = _
    exact sound2950 B hB hF
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h2956 : mixedVector B (Sum.inr 2956) = Sparse.eval nodeValue2956 (mixedVector B) := by
    change mixedMoment B node2956 node2956Labels = _
    exact sound2956 B hB hF
  have h2962 : mixedVector B (Sum.inr 2962) = Sparse.eval nodeValue2962 (mixedVector B) := by
    change mixedMoment B node2962 node2962Labels = _
    exact sound2962 B hB hF
  have h3096 : mixedVector B (Sum.inr 3096) = Sparse.eval nodeValue3096 (mixedVector B) := by
    change mixedMoment B node3096 node3096Labels = _
    exact sound3096 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm754, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2950, h2952, h2956, h2962, h3096, h3572, h4083, reducedSource653] using sourceEq754 B hB

theorem rowSound653 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row653 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck653, numericCheck653, reducedZero653 B hB hF, mul_zero]

theorem reducedZero654 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource654 (mixedVector B) = 0 := by
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h3096 : mixedVector B (Sum.inr 3096) = Sparse.eval nodeValue3096 (mixedVector B) := by
    change mixedMoment B node3096 node3096Labels = _
    exact sound3096 B hB hF
  have h3503 : mixedVector B (Sum.inr 3503) = Sparse.eval nodeValue3503 (mixedVector B) := by
    change mixedMoment B node3503 node3503Labels = _
    exact sound3503 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm755, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2107, h3096, h3503, h3572, h3581, h3583, h4083, reducedSource654] using sourceEq755 B hB

theorem rowSound654 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row654 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck654, numericCheck654, reducedZero654 B hB hF, mul_zero]

theorem reducedZero655 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource655 (mixedVector B) = 0 := by
  have h2995 : mixedVector B (Sum.inr 2995) = Sparse.eval nodeValue2995 (mixedVector B) := by
    change mixedMoment B node2995 node2995Labels = _
    exact sound2995 B hB hF
  have h3507 : mixedVector B (Sum.inr 3507) = Sparse.eval nodeValue3507 (mixedVector B) := by
    change mixedMoment B node3507 node3507Labels = _
    exact sound3507 B hB hF
  have h3550 : mixedVector B (Sum.inr 3550) = Sparse.eval nodeValue3550 (mixedVector B) := by
    change mixedMoment B node3550 node3550Labels = _
    exact sound3550 B hB hF
  have h3552 : mixedVector B (Sum.inr 3552) = Sparse.eval nodeValue3552 (mixedVector B) := by
    change mixedMoment B node3552 node3552Labels = _
    exact sound3552 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm756, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2995, h3507, h3550, h3552, h3572, h4083, reducedSource655] using sourceEq756 B hB

theorem rowSound655 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row655 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck655, numericCheck655, reducedZero655 B hB hF, mul_zero]

theorem sourceRowsAt640 : MixedData.sourceRows (640 : Fin 2425) =
    MixedData.row640 := by decide +kernel

theorem sourceRowsAt641 : MixedData.sourceRows (641 : Fin 2425) =
    MixedData.row641 := by decide +kernel

theorem sourceRowsAt642 : MixedData.sourceRows (642 : Fin 2425) =
    MixedData.row642 := by decide +kernel

theorem sourceRowsAt643 : MixedData.sourceRows (643 : Fin 2425) =
    MixedData.row643 := by decide +kernel

theorem sourceRowsAt644 : MixedData.sourceRows (644 : Fin 2425) =
    MixedData.row644 := by decide +kernel

theorem sourceRowsAt645 : MixedData.sourceRows (645 : Fin 2425) =
    MixedData.row645 := by decide +kernel

theorem sourceRowsAt646 : MixedData.sourceRows (646 : Fin 2425) =
    MixedData.row646 := by decide +kernel

theorem sourceRowsAt647 : MixedData.sourceRows (647 : Fin 2425) =
    MixedData.row647 := by decide +kernel

theorem sourceRowsAt648 : MixedData.sourceRows (648 : Fin 2425) =
    MixedData.row648 := by decide +kernel

theorem sourceRowsAt649 : MixedData.sourceRows (649 : Fin 2425) =
    MixedData.row649 := by decide +kernel

theorem sourceRowsAt650 : MixedData.sourceRows (650 : Fin 2425) =
    MixedData.row650 := by decide +kernel

theorem sourceRowsAt651 : MixedData.sourceRows (651 : Fin 2425) =
    MixedData.row651 := by decide +kernel

theorem sourceRowsAt652 : MixedData.sourceRows (652 : Fin 2425) =
    MixedData.row652 := by decide +kernel

theorem sourceRowsAt653 : MixedData.sourceRows (653 : Fin 2425) =
    MixedData.row653 := by decide +kernel

theorem sourceRowsAt654 : MixedData.sourceRows (654 : Fin 2425) =
    MixedData.row654 := by decide +kernel

theorem sourceRowsAt655 : MixedData.sourceRows (655 : Fin 2425) =
    MixedData.row655 := by decide +kernel

theorem chunkSound40 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 40) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 640 ∨ k.val = 641 ∨ k.val = 642 ∨ k.val = 643 ∨ k.val = 644 ∨ k.val = 645 ∨ k.val = 646 ∨ k.val = 647 ∨ k.val = 648 ∨ k.val = 649 ∨ k.val = 650 ∨ k.val = 651 ∨ k.val = 652 ∨ k.val = 653 ∨ k.val = 654 ∨ k.val = 655 := by omega
  rcases heq with h640 | h641 | h642 | h643 | h644 | h645 | h646 | h647 | h648 | h649 | h650 | h651 | h652 | h653 | h654 | h655
  · have he : k = (640 : Fin 2425) := Fin.ext h640
    subst k
    rw [sourceRowsAt640]
    exact rowSound640 B hB hF
  · have he : k = (641 : Fin 2425) := Fin.ext h641
    subst k
    rw [sourceRowsAt641]
    exact rowSound641 B hB hF
  · have he : k = (642 : Fin 2425) := Fin.ext h642
    subst k
    rw [sourceRowsAt642]
    exact rowSound642 B hB hF
  · have he : k = (643 : Fin 2425) := Fin.ext h643
    subst k
    rw [sourceRowsAt643]
    exact rowSound643 B hB hF
  · have he : k = (644 : Fin 2425) := Fin.ext h644
    subst k
    rw [sourceRowsAt644]
    exact rowSound644 B hB hF
  · have he : k = (645 : Fin 2425) := Fin.ext h645
    subst k
    rw [sourceRowsAt645]
    exact rowSound645 B hB hF
  · have he : k = (646 : Fin 2425) := Fin.ext h646
    subst k
    rw [sourceRowsAt646]
    exact rowSound646 B hB hF
  · have he : k = (647 : Fin 2425) := Fin.ext h647
    subst k
    rw [sourceRowsAt647]
    exact rowSound647 B hB hF
  · have he : k = (648 : Fin 2425) := Fin.ext h648
    subst k
    rw [sourceRowsAt648]
    exact rowSound648 B hB hF
  · have he : k = (649 : Fin 2425) := Fin.ext h649
    subst k
    rw [sourceRowsAt649]
    exact rowSound649 B hB hF
  · have he : k = (650 : Fin 2425) := Fin.ext h650
    subst k
    rw [sourceRowsAt650]
    exact rowSound650 B hB hF
  · have he : k = (651 : Fin 2425) := Fin.ext h651
    subst k
    rw [sourceRowsAt651]
    exact rowSound651 B hB hF
  · have he : k = (652 : Fin 2425) := Fin.ext h652
    subst k
    rw [sourceRowsAt652]
    exact rowSound652 B hB hF
  · have he : k = (653 : Fin 2425) := Fin.ext h653
    subst k
    rw [sourceRowsAt653]
    exact rowSound653 B hB hF
  · have he : k = (654 : Fin 2425) := Fin.ext h654
    subst k
    rw [sourceRowsAt654]
    exact rowSound654 B hB hF
  · have he : k = (655 : Fin 2425) := Fin.ext h655
    subst k
    rw [sourceRowsAt655]
    exact rowSound655 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
