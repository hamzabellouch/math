import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons10

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node640 node640Labels = Sparse.eval nodeValue640 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 640) = mixedMoment B node640 node640Labels := rfl
  simpa [nodeValue640, Sparse.eval] using hc.symm

theorem sound641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node641 node641Labels = Sparse.eval nodeValue641 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 641) = mixedMoment B node641 node641Labels := rfl
  simpa [nodeValue641, Sparse.eval] using hc.symm

theorem sound642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node642 node642Labels = Sparse.eval nodeValue642 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 642) = mixedMoment B node642 node642Labels := rfl
  simpa [nodeValue642, Sparse.eval] using hc.symm

theorem sound643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node643 node643Labels = Sparse.eval nodeValue643 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 643) = mixedMoment B node643 node643Labels := rfl
  simpa [nodeValue643, Sparse.eval] using hc.symm

theorem sound644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node644 node644Labels = Sparse.eval nodeValue644 (mixedVector B) := by
  have h := singleton644 B _hB
  rw [sound26 B _hB _hF] at h
  norm_num [nodeValue644, nodeValue26, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node645 node645Labels = Sparse.eval nodeValue645 (mixedVector B) := by
  have h := singleton645 B _hB
  rw [sound31 B _hB _hF] at h
  norm_num [nodeValue645, nodeValue31, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node646 node646Labels = Sparse.eval nodeValue646 (mixedVector B) := by
  have h := singleton646 B _hB
  rw [sound23 B _hB _hF] at h
  norm_num [nodeValue646, nodeValue23, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node647 node647Labels = Sparse.eval nodeValue647 (mixedVector B) := by
  have h := singleton647 B _hB
  rw [sound28 B _hB _hF] at h
  norm_num [nodeValue647, nodeValue28, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node648 node648Labels = Sparse.eval nodeValue648 (mixedVector B) := by
  have h := singleton648 B _hB
  rw [sound33 B _hB _hF] at h
  norm_num [nodeValue648, nodeValue33, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node649 node649Labels = Sparse.eval nodeValue649 (mixedVector B) := by
  have h := singleton649 B _hB
  rw [sound34 B _hB _hF] at h
  norm_num [nodeValue649, nodeValue34, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node650 node650Labels = Sparse.eval nodeValue650 (mixedVector B) := by
  have h := singleton650 B _hB
  rw [sound35 B _hB _hF] at h
  norm_num [nodeValue650, nodeValue35, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node651 node651Labels = Sparse.eval nodeValue651 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 651) = mixedMoment B node651 node651Labels := rfl
  simpa [nodeValue651, Sparse.eval] using hc.symm

theorem sound652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node652 node652Labels = Sparse.eval nodeValue652 (mixedVector B) := by
  have h := singleton652 B _hB
  rw [sound25 B _hB _hF] at h
  norm_num [nodeValue652, nodeValue25, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node653 node653Labels = Sparse.eval nodeValue653 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 653) = mixedMoment B node653 node653Labels := rfl
  simpa [nodeValue653, Sparse.eval] using hc.symm

theorem sound654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node654 node654Labels = Sparse.eval nodeValue654 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 654) = mixedMoment B node654 node654Labels := rfl
  simpa [nodeValue654, Sparse.eval] using hc.symm

theorem sound655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node655 node655Labels = Sparse.eval nodeValue655 (mixedVector B) := by
  have h := singleton655 B _hB
  rw [sound38 B _hB _hF] at h
  norm_num [nodeValue655, nodeValue38, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node656 node656Labels = Sparse.eval nodeValue656 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 656) = mixedMoment B node656 node656Labels := rfl
  simpa [nodeValue656, Sparse.eval] using hc.symm

theorem sound657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node657 node657Labels = Sparse.eval nodeValue657 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 657) = mixedMoment B node657 node657Labels := rfl
  simpa [nodeValue657, Sparse.eval] using hc.symm

theorem sound658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node658 node658Labels = Sparse.eval nodeValue658 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 658) = mixedMoment B node658 node658Labels := rfl
  simpa [nodeValue658, Sparse.eval] using hc.symm

theorem sound659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node659 node659Labels = Sparse.eval nodeValue659 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 659) = mixedMoment B node659 node659Labels := rfl
  simpa [nodeValue659, Sparse.eval] using hc.symm

theorem sound660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node660 node660Labels = Sparse.eval nodeValue660 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 660) = mixedMoment B node660 node660Labels := rfl
  simpa [nodeValue660, Sparse.eval] using hc.symm

theorem sound661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node661 node661Labels = Sparse.eval nodeValue661 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 661) = mixedMoment B node661 node661Labels := rfl
  simpa [nodeValue661, Sparse.eval] using hc.symm

theorem sound662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node662 node662Labels = Sparse.eval nodeValue662 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 662) = mixedMoment B node662 node662Labels := rfl
  simpa [nodeValue662, Sparse.eval] using hc.symm

theorem sound663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node663 node663Labels = Sparse.eval nodeValue663 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 663) = mixedMoment B node663 node663Labels := rfl
  simpa [nodeValue663, Sparse.eval] using hc.symm

theorem sound664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node664 node664Labels = Sparse.eval nodeValue664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 664) = mixedMoment B node664 node664Labels := rfl
  simpa [nodeValue664, Sparse.eval] using hc.symm

theorem sound665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node665 node665Labels = Sparse.eval nodeValue665 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 665) = mixedMoment B node665 node665Labels := rfl
  simpa [nodeValue665, Sparse.eval] using hc.symm

theorem sound666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node666 node666Labels = Sparse.eval nodeValue666 (mixedVector B) := by
  simpa only [nodeValue666, Sparse.eval_nil] using zero666 B _hB _hF

theorem sound667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node667 node667Labels = Sparse.eval nodeValue667 (mixedVector B) := by
  simpa only [nodeValue667, Sparse.eval_nil] using zero667 B _hB _hF

theorem sound668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node668 node668Labels = Sparse.eval nodeValue668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 668) = mixedMoment B node668 node668Labels := rfl
  simpa [nodeValue668, Sparse.eval] using hc.symm

theorem sound669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node669 node669Labels = Sparse.eval nodeValue669 (mixedVector B) := by
  simpa only [nodeValue669, Sparse.eval_nil] using zero669 B _hB _hF

theorem sound670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node670 node670Labels = Sparse.eval nodeValue670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 670) = mixedMoment B node670 node670Labels := rfl
  simpa [nodeValue670, Sparse.eval] using hc.symm

theorem sound671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node671 node671Labels = Sparse.eval nodeValue671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 671) = mixedMoment B node671 node671Labels := rfl
  simpa [nodeValue671, Sparse.eval] using hc.symm

theorem sound672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node672 node672Labels = Sparse.eval nodeValue672 (mixedVector B) := by
  simpa only [nodeValue672, Sparse.eval_nil] using zero672 B _hB _hF

theorem sound673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node673 node673Labels = Sparse.eval nodeValue673 (mixedVector B) := by
  simpa only [nodeValue673, Sparse.eval_nil] using zero673 B _hB _hF

theorem sound674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node674 node674Labels = Sparse.eval nodeValue674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 674) = mixedMoment B node674 node674Labels := rfl
  simpa [nodeValue674, Sparse.eval] using hc.symm

theorem sound675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node675 node675Labels = Sparse.eval nodeValue675 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 675) = mixedMoment B node675 node675Labels := rfl
  simpa [nodeValue675, Sparse.eval] using hc.symm

theorem sound676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node676 node676Labels = Sparse.eval nodeValue676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 676) = mixedMoment B node676 node676Labels := rfl
  simpa [nodeValue676, Sparse.eval] using hc.symm

theorem sound677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node677 node677Labels = Sparse.eval nodeValue677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 677) = mixedMoment B node677 node677Labels := rfl
  simpa [nodeValue677, Sparse.eval] using hc.symm

theorem sound678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node678 node678Labels = Sparse.eval nodeValue678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 678) = mixedMoment B node678 node678Labels := rfl
  simpa [nodeValue678, Sparse.eval] using hc.symm

theorem sound679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node679 node679Labels = Sparse.eval nodeValue679 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 679) = mixedMoment B node679 node679Labels := rfl
  simpa [nodeValue679, Sparse.eval] using hc.symm

theorem sound680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node680 node680Labels = Sparse.eval nodeValue680 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 680) = mixedMoment B node680 node680Labels := rfl
  simpa [nodeValue680, Sparse.eval] using hc.symm

theorem sound681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node681 node681Labels = Sparse.eval nodeValue681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 681) = mixedMoment B node681 node681Labels := rfl
  simpa [nodeValue681, Sparse.eval] using hc.symm

theorem sound682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node682 node682Labels = Sparse.eval nodeValue682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 682) = mixedMoment B node682 node682Labels := rfl
  simpa [nodeValue682, Sparse.eval] using hc.symm

theorem sound683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node683 node683Labels = Sparse.eval nodeValue683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 683) = mixedMoment B node683 node683Labels := rfl
  simpa [nodeValue683, Sparse.eval] using hc.symm

theorem sound684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node684 node684Labels = Sparse.eval nodeValue684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 684) = mixedMoment B node684 node684Labels := rfl
  simpa [nodeValue684, Sparse.eval] using hc.symm

theorem sound685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node685 node685Labels = Sparse.eval nodeValue685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 685) = mixedMoment B node685 node685Labels := rfl
  simpa [nodeValue685, Sparse.eval] using hc.symm

theorem sound686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node686 node686Labels = Sparse.eval nodeValue686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 686) = mixedMoment B node686 node686Labels := rfl
  simpa [nodeValue686, Sparse.eval] using hc.symm

theorem sound687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node687 node687Labels = Sparse.eval nodeValue687 (mixedVector B) := by
  simpa only [nodeValue687, Sparse.eval_nil] using zero687 B _hB _hF

theorem sound688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node688 node688Labels = Sparse.eval nodeValue688 (mixedVector B) := by
  simpa only [nodeValue688, Sparse.eval_nil] using zero688 B _hB _hF

theorem sound689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node689 node689Labels = Sparse.eval nodeValue689 (mixedVector B) := by
  simpa only [nodeValue689, Sparse.eval_nil] using zero689 B _hB _hF

theorem sound690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node690 node690Labels = Sparse.eval nodeValue690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 690) = mixedMoment B node690 node690Labels := rfl
  simpa [nodeValue690, Sparse.eval] using hc.symm

theorem sound691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node691 node691Labels = Sparse.eval nodeValue691 (mixedVector B) := by
  simpa only [nodeValue691, Sparse.eval_nil] using zero691 B _hB _hF

theorem sound692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node692 node692Labels = Sparse.eval nodeValue692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 692) = mixedMoment B node692 node692Labels := rfl
  simpa [nodeValue692, Sparse.eval] using hc.symm

theorem sound693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node693 node693Labels = Sparse.eval nodeValue693 (mixedVector B) := by
  simpa only [nodeValue693, Sparse.eval_nil] using zero693 B _hB _hF

theorem sound694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node694 node694Labels = Sparse.eval nodeValue694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 694) = mixedMoment B node694 node694Labels := rfl
  simpa [nodeValue694, Sparse.eval] using hc.symm

theorem sound695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node695 node695Labels = Sparse.eval nodeValue695 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 695) = mixedMoment B node695 node695Labels := rfl
  simpa [nodeValue695, Sparse.eval] using hc.symm

theorem sound696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node696 node696Labels = Sparse.eval nodeValue696 (mixedVector B) := by
  simpa only [nodeValue696, Sparse.eval_nil] using zero696 B _hB _hF

theorem sound697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node697 node697Labels = Sparse.eval nodeValue697 (mixedVector B) := by
  simpa only [nodeValue697, Sparse.eval_nil] using zero697 B _hB _hF

theorem sound698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node698 node698Labels = Sparse.eval nodeValue698 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 698) = mixedMoment B node698 node698Labels := rfl
  simpa [nodeValue698, Sparse.eval] using hc.symm

theorem sound699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node699 node699Labels = Sparse.eval nodeValue699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 699) = mixedMoment B node699 node699Labels := rfl
  simpa [nodeValue699, Sparse.eval] using hc.symm

theorem sound700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node700 node700Labels = Sparse.eval nodeValue700 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 700) = mixedMoment B node700 node700Labels := rfl
  simpa [nodeValue700, Sparse.eval] using hc.symm

theorem sound701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node701 node701Labels = Sparse.eval nodeValue701 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 701) = mixedMoment B node701 node701Labels := rfl
  simpa [nodeValue701, Sparse.eval] using hc.symm

theorem sound702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node702 node702Labels = Sparse.eval nodeValue702 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 702) = mixedMoment B node702 node702Labels := rfl
  simpa [nodeValue702, Sparse.eval] using hc.symm

theorem sound703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node703 node703Labels = Sparse.eval nodeValue703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 703) = mixedMoment B node703 node703Labels := rfl
  simpa [nodeValue703, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
