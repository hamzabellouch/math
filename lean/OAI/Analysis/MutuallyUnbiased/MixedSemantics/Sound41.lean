import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons41

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2624 node2624Labels = Sparse.eval nodeValue2624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2624) = mixedMoment B node2624 node2624Labels := rfl
  simpa [nodeValue2624, Sparse.eval] using hc.symm

theorem sound2625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2625 node2625Labels = Sparse.eval nodeValue2625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2625) = mixedMoment B node2625 node2625Labels := rfl
  simpa [nodeValue2625, Sparse.eval] using hc.symm

theorem sound2626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2626 node2626Labels = Sparse.eval nodeValue2626 (mixedVector B) := by
  have h := singleton2626 B _hB
  rw [sound201 B _hB _hF] at h
  norm_num [nodeValue2626, nodeValue201, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2627 node2627Labels = Sparse.eval nodeValue2627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2627) = mixedMoment B node2627 node2627Labels := rfl
  simpa [nodeValue2627, Sparse.eval] using hc.symm

theorem sound2628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2628 node2628Labels = Sparse.eval nodeValue2628 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2628) = mixedMoment B node2628 node2628Labels := rfl
  simpa [nodeValue2628, Sparse.eval] using hc.symm

theorem sound2629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2629 node2629Labels = Sparse.eval nodeValue2629 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2629) = mixedMoment B node2629 node2629Labels := rfl
  simpa [nodeValue2629, Sparse.eval] using hc.symm

theorem sound2630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2630 node2630Labels = Sparse.eval nodeValue2630 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2630) = mixedMoment B node2630 node2630Labels := rfl
  simpa [nodeValue2630, Sparse.eval] using hc.symm

theorem sound2631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2631 node2631Labels = Sparse.eval nodeValue2631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2631) = mixedMoment B node2631 node2631Labels := rfl
  simpa [nodeValue2631, Sparse.eval] using hc.symm

theorem sound2632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2632 node2632Labels = Sparse.eval nodeValue2632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2632) = mixedMoment B node2632 node2632Labels := rfl
  simpa [nodeValue2632, Sparse.eval] using hc.symm

theorem sound2633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2633 node2633Labels = Sparse.eval nodeValue2633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2633) = mixedMoment B node2633 node2633Labels := rfl
  simpa [nodeValue2633, Sparse.eval] using hc.symm

theorem sound2634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2634 node2634Labels = Sparse.eval nodeValue2634 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2634) = mixedMoment B node2634 node2634Labels := rfl
  simpa [nodeValue2634, Sparse.eval] using hc.symm

theorem sound2635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2635 node2635Labels = Sparse.eval nodeValue2635 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2635) = mixedMoment B node2635 node2635Labels := rfl
  simpa [nodeValue2635, Sparse.eval] using hc.symm

theorem sound2636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2636 node2636Labels = Sparse.eval nodeValue2636 (mixedVector B) := by
  have h := singleton2636 B _hB
  rw [sound351 B _hB _hF] at h
  norm_num [nodeValue2636, nodeValue351, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2637 node2637Labels = Sparse.eval nodeValue2637 (mixedVector B) := by
  have h := singleton2637 B _hB
  rw [sound352 B _hB _hF] at h
  norm_num [nodeValue2637, nodeValue352, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2638 node2638Labels = Sparse.eval nodeValue2638 (mixedVector B) := by
  have h := singleton2638 B _hB
  rw [sound353 B _hB _hF] at h
  norm_num [nodeValue2638, nodeValue353, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2639 node2639Labels = Sparse.eval nodeValue2639 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2639) = mixedMoment B node2639 node2639Labels := rfl
  simpa [nodeValue2639, Sparse.eval] using hc.symm

theorem sound2640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2640 node2640Labels = Sparse.eval nodeValue2640 (mixedVector B) := by
  have h := singleton2640 B _hB
  rw [sound315 B _hB _hF] at h
  norm_num [nodeValue2640, nodeValue315, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2641 node2641Labels = Sparse.eval nodeValue2641 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2641) = mixedMoment B node2641 node2641Labels := rfl
  simpa [nodeValue2641, Sparse.eval] using hc.symm

theorem sound2642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2642 node2642Labels = Sparse.eval nodeValue2642 (mixedVector B) := by
  have h := singleton2642 B _hB
  rw [sound236 B _hB _hF] at h
  norm_num [nodeValue2642, nodeValue236, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2643 node2643Labels = Sparse.eval nodeValue2643 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2643) = mixedMoment B node2643 node2643Labels := rfl
  simpa [nodeValue2643, Sparse.eval] using hc.symm

theorem sound2644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2644 node2644Labels = Sparse.eval nodeValue2644 (mixedVector B) := by
  have h := singleton2644 B _hB
  rw [sound355 B _hB _hF] at h
  norm_num [nodeValue2644, nodeValue355, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2645 node2645Labels = Sparse.eval nodeValue2645 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2645) = mixedMoment B node2645 node2645Labels := rfl
  simpa [nodeValue2645, Sparse.eval] using hc.symm

theorem sound2646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2646 node2646Labels = Sparse.eval nodeValue2646 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2646) = mixedMoment B node2646 node2646Labels := rfl
  simpa [nodeValue2646, Sparse.eval] using hc.symm

theorem sound2647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2647 node2647Labels = Sparse.eval nodeValue2647 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2647) = mixedMoment B node2647 node2647Labels := rfl
  simpa [nodeValue2647, Sparse.eval] using hc.symm

theorem sound2648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2648 node2648Labels = Sparse.eval nodeValue2648 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2648) = mixedMoment B node2648 node2648Labels := rfl
  simpa [nodeValue2648, Sparse.eval] using hc.symm

theorem sound2649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2649 node2649Labels = Sparse.eval nodeValue2649 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2649) = mixedMoment B node2649 node2649Labels := rfl
  simpa [nodeValue2649, Sparse.eval] using hc.symm

theorem sound2650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2650 node2650Labels = Sparse.eval nodeValue2650 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2650) = mixedMoment B node2650 node2650Labels := rfl
  simpa [nodeValue2650, Sparse.eval] using hc.symm

theorem sound2651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2651 node2651Labels = Sparse.eval nodeValue2651 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2651) = mixedMoment B node2651 node2651Labels := rfl
  simpa [nodeValue2651, Sparse.eval] using hc.symm

theorem sound2652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2652 node2652Labels = Sparse.eval nodeValue2652 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2652) = mixedMoment B node2652 node2652Labels := rfl
  simpa [nodeValue2652, Sparse.eval] using hc.symm

theorem sound2653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2653 node2653Labels = Sparse.eval nodeValue2653 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2653) = mixedMoment B node2653 node2653Labels := rfl
  simpa [nodeValue2653, Sparse.eval] using hc.symm

theorem sound2654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2654 node2654Labels = Sparse.eval nodeValue2654 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2654) = mixedMoment B node2654 node2654Labels := rfl
  simpa [nodeValue2654, Sparse.eval] using hc.symm

theorem sound2655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2655 node2655Labels = Sparse.eval nodeValue2655 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2655) = mixedMoment B node2655 node2655Labels := rfl
  simpa [nodeValue2655, Sparse.eval] using hc.symm

theorem sound2656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2656 node2656Labels = Sparse.eval nodeValue2656 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2656) = mixedMoment B node2656 node2656Labels := rfl
  simpa [nodeValue2656, Sparse.eval] using hc.symm

theorem sound2657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2657 node2657Labels = Sparse.eval nodeValue2657 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2657) = mixedMoment B node2657 node2657Labels := rfl
  simpa [nodeValue2657, Sparse.eval] using hc.symm

theorem sound2658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2658 node2658Labels = Sparse.eval nodeValue2658 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2658) = mixedMoment B node2658 node2658Labels := rfl
  simpa [nodeValue2658, Sparse.eval] using hc.symm

theorem sound2659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2659 node2659Labels = Sparse.eval nodeValue2659 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2659) = mixedMoment B node2659 node2659Labels := rfl
  simpa [nodeValue2659, Sparse.eval] using hc.symm

theorem sound2660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2660 node2660Labels = Sparse.eval nodeValue2660 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2660) = mixedMoment B node2660 node2660Labels := rfl
  simpa [nodeValue2660, Sparse.eval] using hc.symm

theorem sound2661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2661 node2661Labels = Sparse.eval nodeValue2661 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2661) = mixedMoment B node2661 node2661Labels := rfl
  simpa [nodeValue2661, Sparse.eval] using hc.symm

theorem sound2662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2662 node2662Labels = Sparse.eval nodeValue2662 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2662) = mixedMoment B node2662 node2662Labels := rfl
  simpa [nodeValue2662, Sparse.eval] using hc.symm

theorem sound2663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2663 node2663Labels = Sparse.eval nodeValue2663 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2663) = mixedMoment B node2663 node2663Labels := rfl
  simpa [nodeValue2663, Sparse.eval] using hc.symm

theorem sound2664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2664 node2664Labels = Sparse.eval nodeValue2664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2664) = mixedMoment B node2664 node2664Labels := rfl
  simpa [nodeValue2664, Sparse.eval] using hc.symm

theorem sound2665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2665 node2665Labels = Sparse.eval nodeValue2665 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2665) = mixedMoment B node2665 node2665Labels := rfl
  simpa [nodeValue2665, Sparse.eval] using hc.symm

theorem sound2666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2666 node2666Labels = Sparse.eval nodeValue2666 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2666) = mixedMoment B node2666 node2666Labels := rfl
  simpa [nodeValue2666, Sparse.eval] using hc.symm

theorem sound2667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2667 node2667Labels = Sparse.eval nodeValue2667 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2667) = mixedMoment B node2667 node2667Labels := rfl
  simpa [nodeValue2667, Sparse.eval] using hc.symm

theorem sound2668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2668 node2668Labels = Sparse.eval nodeValue2668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2668) = mixedMoment B node2668 node2668Labels := rfl
  simpa [nodeValue2668, Sparse.eval] using hc.symm

theorem sound2669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2669 node2669Labels = Sparse.eval nodeValue2669 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2669) = mixedMoment B node2669 node2669Labels := rfl
  simpa [nodeValue2669, Sparse.eval] using hc.symm

theorem sound2670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2670 node2670Labels = Sparse.eval nodeValue2670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2670) = mixedMoment B node2670 node2670Labels := rfl
  simpa [nodeValue2670, Sparse.eval] using hc.symm

theorem sound2671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2671 node2671Labels = Sparse.eval nodeValue2671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2671) = mixedMoment B node2671 node2671Labels := rfl
  simpa [nodeValue2671, Sparse.eval] using hc.symm

theorem sound2672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2672 node2672Labels = Sparse.eval nodeValue2672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2672) = mixedMoment B node2672 node2672Labels := rfl
  simpa [nodeValue2672, Sparse.eval] using hc.symm

theorem sound2673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2673 node2673Labels = Sparse.eval nodeValue2673 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2673) = mixedMoment B node2673 node2673Labels := rfl
  simpa [nodeValue2673, Sparse.eval] using hc.symm

theorem sound2674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2674 node2674Labels = Sparse.eval nodeValue2674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2674) = mixedMoment B node2674 node2674Labels := rfl
  simpa [nodeValue2674, Sparse.eval] using hc.symm

theorem sound2675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2675 node2675Labels = Sparse.eval nodeValue2675 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2675) = mixedMoment B node2675 node2675Labels := rfl
  simpa [nodeValue2675, Sparse.eval] using hc.symm

theorem sound2676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2676 node2676Labels = Sparse.eval nodeValue2676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2676) = mixedMoment B node2676 node2676Labels := rfl
  simpa [nodeValue2676, Sparse.eval] using hc.symm

theorem sound2677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2677 node2677Labels = Sparse.eval nodeValue2677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2677) = mixedMoment B node2677 node2677Labels := rfl
  simpa [nodeValue2677, Sparse.eval] using hc.symm

theorem sound2678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2678 node2678Labels = Sparse.eval nodeValue2678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2678) = mixedMoment B node2678 node2678Labels := rfl
  simpa [nodeValue2678, Sparse.eval] using hc.symm

theorem sound2679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2679 node2679Labels = Sparse.eval nodeValue2679 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2679) = mixedMoment B node2679 node2679Labels := rfl
  simpa [nodeValue2679, Sparse.eval] using hc.symm

theorem sound2680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2680 node2680Labels = Sparse.eval nodeValue2680 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2680) = mixedMoment B node2680 node2680Labels := rfl
  simpa [nodeValue2680, Sparse.eval] using hc.symm

theorem sound2681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2681 node2681Labels = Sparse.eval nodeValue2681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2681) = mixedMoment B node2681 node2681Labels := rfl
  simpa [nodeValue2681, Sparse.eval] using hc.symm

theorem sound2682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2682 node2682Labels = Sparse.eval nodeValue2682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2682) = mixedMoment B node2682 node2682Labels := rfl
  simpa [nodeValue2682, Sparse.eval] using hc.symm

theorem sound2683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2683 node2683Labels = Sparse.eval nodeValue2683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2683) = mixedMoment B node2683 node2683Labels := rfl
  simpa [nodeValue2683, Sparse.eval] using hc.symm

theorem sound2684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2684 node2684Labels = Sparse.eval nodeValue2684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2684) = mixedMoment B node2684 node2684Labels := rfl
  simpa [nodeValue2684, Sparse.eval] using hc.symm

theorem sound2685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2685 node2685Labels = Sparse.eval nodeValue2685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2685) = mixedMoment B node2685 node2685Labels := rfl
  simpa [nodeValue2685, Sparse.eval] using hc.symm

theorem sound2686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2686 node2686Labels = Sparse.eval nodeValue2686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2686) = mixedMoment B node2686 node2686Labels := rfl
  simpa [nodeValue2686, Sparse.eval] using hc.symm

theorem sound2687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2687 node2687Labels = Sparse.eval nodeValue2687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2687) = mixedMoment B node2687 node2687Labels := rfl
  simpa [nodeValue2687, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
