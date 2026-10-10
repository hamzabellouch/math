import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound87
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2784 : keyMomentRows (2784 : Fin 2886) =
    keyMomentRow2784 := by decide +kernel

theorem keyMomentRowsAt2785 : keyMomentRows (2785 : Fin 2886) =
    keyMomentRow2785 := by decide +kernel

theorem keyMomentRowsAt2786 : keyMomentRows (2786 : Fin 2886) =
    keyMomentRow2786 := by decide +kernel

theorem keyMomentRowsAt2787 : keyMomentRows (2787 : Fin 2886) =
    keyMomentRow2787 := by decide +kernel

theorem keyMomentRowsAt2788 : keyMomentRows (2788 : Fin 2886) =
    keyMomentRow2788 := by decide +kernel

theorem keyMomentRowsAt2789 : keyMomentRows (2789 : Fin 2886) =
    keyMomentRow2789 := by decide +kernel

theorem keyMomentRowsAt2790 : keyMomentRows (2790 : Fin 2886) =
    keyMomentRow2790 := by decide +kernel

theorem keyMomentRowsAt2791 : keyMomentRows (2791 : Fin 2886) =
    keyMomentRow2791 := by decide +kernel

theorem keyMomentRowsAt2792 : keyMomentRows (2792 : Fin 2886) =
    keyMomentRow2792 := by decide +kernel

theorem keyMomentRowsAt2793 : keyMomentRows (2793 : Fin 2886) =
    keyMomentRow2793 := by decide +kernel

theorem keyMomentRowsAt2794 : keyMomentRows (2794 : Fin 2886) =
    keyMomentRow2794 := by decide +kernel

theorem keyMomentRowsAt2795 : keyMomentRows (2795 : Fin 2886) =
    keyMomentRow2795 := by decide +kernel

theorem keyMomentRowsAt2796 : keyMomentRows (2796 : Fin 2886) =
    keyMomentRow2796 := by decide +kernel

theorem keyMomentRowsAt2797 : keyMomentRows (2797 : Fin 2886) =
    keyMomentRow2797 := by decide +kernel

theorem keyMomentRowsAt2798 : keyMomentRows (2798 : Fin 2886) =
    keyMomentRow2798 := by decide +kernel

theorem keyMomentRowsAt2799 : keyMomentRows (2799 : Fin 2886) =
    keyMomentRow2799 := by decide +kernel

theorem keyMomentRowsAt2800 : keyMomentRows (2800 : Fin 2886) =
    keyMomentRow2800 := by decide +kernel

theorem keyMomentRowsAt2801 : keyMomentRows (2801 : Fin 2886) =
    keyMomentRow2801 := by decide +kernel

theorem keyMomentRowsAt2802 : keyMomentRows (2802 : Fin 2886) =
    keyMomentRow2802 := by decide +kernel

theorem keyMomentRowsAt2803 : keyMomentRows (2803 : Fin 2886) =
    keyMomentRow2803 := by decide +kernel

theorem keyMomentRowsAt2804 : keyMomentRows (2804 : Fin 2886) =
    keyMomentRow2804 := by decide +kernel

theorem keyMomentRowsAt2805 : keyMomentRows (2805 : Fin 2886) =
    keyMomentRow2805 := by decide +kernel

theorem keyMomentRowsAt2806 : keyMomentRows (2806 : Fin 2886) =
    keyMomentRow2806 := by decide +kernel

theorem keyMomentRowsAt2807 : keyMomentRows (2807 : Fin 2886) =
    keyMomentRow2807 := by decide +kernel

theorem keyMomentRowsAt2808 : keyMomentRows (2808 : Fin 2886) =
    keyMomentRow2808 := by decide +kernel

theorem keyMomentRowsAt2809 : keyMomentRows (2809 : Fin 2886) =
    keyMomentRow2809 := by decide +kernel

theorem keyMomentRowsAt2810 : keyMomentRows (2810 : Fin 2886) =
    keyMomentRow2810 := by decide +kernel

theorem keyMomentRowsAt2811 : keyMomentRows (2811 : Fin 2886) =
    keyMomentRow2811 := by decide +kernel

theorem keyMomentRowsAt2812 : keyMomentRows (2812 : Fin 2886) =
    keyMomentRow2812 := by decide +kernel

theorem keyMomentRowsAt2813 : keyMomentRows (2813 : Fin 2886) =
    keyMomentRow2813 := by decide +kernel

theorem keyMomentRowsAt2814 : keyMomentRows (2814 : Fin 2886) =
    keyMomentRow2814 := by decide +kernel

theorem keyMomentRowsAt2815 : keyMomentRows (2815 : Fin 2886) =
    keyMomentRow2815 := by decide +kernel

theorem keyMomentChunkSound87 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 87) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2784 ∨ k.val = 2785 ∨ k.val = 2786 ∨ k.val = 2787 ∨ k.val = 2788 ∨ k.val = 2789 ∨ k.val = 2790 ∨ k.val = 2791 ∨ k.val = 2792 ∨ k.val = 2793 ∨ k.val = 2794 ∨ k.val = 2795 ∨ k.val = 2796 ∨ k.val = 2797 ∨ k.val = 2798 ∨ k.val = 2799 ∨ k.val = 2800 ∨ k.val = 2801 ∨ k.val = 2802 ∨ k.val = 2803 ∨ k.val = 2804 ∨ k.val = 2805 ∨ k.val = 2806 ∨ k.val = 2807 ∨ k.val = 2808 ∨ k.val = 2809 ∨ k.val = 2810 ∨ k.val = 2811 ∨ k.val = 2812 ∨ k.val = 2813 ∨ k.val = 2814 ∨ k.val = 2815 := by omega
  rcases heq with h2784 | h2785 | h2786 | h2787 | h2788 | h2789 | h2790 | h2791 | h2792 | h2793 | h2794 | h2795 | h2796 | h2797 | h2798 | h2799 | h2800 | h2801 | h2802 | h2803 | h2804 | h2805 | h2806 | h2807 | h2808 | h2809 | h2810 | h2811 | h2812 | h2813 | h2814 | h2815
  · have he : k = (2784 : Fin 2886) := Fin.ext h2784
    subst k
    rw [keyMomentRowsAt2784]
    exact keyMoment2784 B hB
  · have he : k = (2785 : Fin 2886) := Fin.ext h2785
    subst k
    rw [keyMomentRowsAt2785]
    exact keyMoment2785 B hB
  · have he : k = (2786 : Fin 2886) := Fin.ext h2786
    subst k
    rw [keyMomentRowsAt2786]
    exact keyMoment2786 B hB
  · have he : k = (2787 : Fin 2886) := Fin.ext h2787
    subst k
    rw [keyMomentRowsAt2787]
    exact keyMoment2787 B hB
  · have he : k = (2788 : Fin 2886) := Fin.ext h2788
    subst k
    rw [keyMomentRowsAt2788]
    exact keyMoment2788 B hB
  · have he : k = (2789 : Fin 2886) := Fin.ext h2789
    subst k
    rw [keyMomentRowsAt2789]
    exact keyMoment2789 B hB
  · have he : k = (2790 : Fin 2886) := Fin.ext h2790
    subst k
    rw [keyMomentRowsAt2790]
    exact keyMoment2790 B hB
  · have he : k = (2791 : Fin 2886) := Fin.ext h2791
    subst k
    rw [keyMomentRowsAt2791]
    exact keyMoment2791 B hB
  · have he : k = (2792 : Fin 2886) := Fin.ext h2792
    subst k
    rw [keyMomentRowsAt2792]
    exact keyMoment2792 B hB
  · have he : k = (2793 : Fin 2886) := Fin.ext h2793
    subst k
    rw [keyMomentRowsAt2793]
    exact keyMoment2793 B hB
  · have he : k = (2794 : Fin 2886) := Fin.ext h2794
    subst k
    rw [keyMomentRowsAt2794]
    exact keyMoment2794 B hB
  · have he : k = (2795 : Fin 2886) := Fin.ext h2795
    subst k
    rw [keyMomentRowsAt2795]
    exact keyMoment2795 B hB
  · have he : k = (2796 : Fin 2886) := Fin.ext h2796
    subst k
    rw [keyMomentRowsAt2796]
    exact keyMoment2796 B hB
  · have he : k = (2797 : Fin 2886) := Fin.ext h2797
    subst k
    rw [keyMomentRowsAt2797]
    exact keyMoment2797 B hB
  · have he : k = (2798 : Fin 2886) := Fin.ext h2798
    subst k
    rw [keyMomentRowsAt2798]
    exact keyMoment2798 B hB
  · have he : k = (2799 : Fin 2886) := Fin.ext h2799
    subst k
    rw [keyMomentRowsAt2799]
    exact keyMoment2799 B hB
  · have he : k = (2800 : Fin 2886) := Fin.ext h2800
    subst k
    rw [keyMomentRowsAt2800]
    exact keyMoment2800 B hB
  · have he : k = (2801 : Fin 2886) := Fin.ext h2801
    subst k
    rw [keyMomentRowsAt2801]
    exact keyMoment2801 B hB
  · have he : k = (2802 : Fin 2886) := Fin.ext h2802
    subst k
    rw [keyMomentRowsAt2802]
    exact keyMoment2802 B hB
  · have he : k = (2803 : Fin 2886) := Fin.ext h2803
    subst k
    rw [keyMomentRowsAt2803]
    exact keyMoment2803 B hB
  · have he : k = (2804 : Fin 2886) := Fin.ext h2804
    subst k
    rw [keyMomentRowsAt2804]
    exact keyMoment2804 B hB
  · have he : k = (2805 : Fin 2886) := Fin.ext h2805
    subst k
    rw [keyMomentRowsAt2805]
    exact keyMoment2805 B hB
  · have he : k = (2806 : Fin 2886) := Fin.ext h2806
    subst k
    rw [keyMomentRowsAt2806]
    exact keyMoment2806 B hB
  · have he : k = (2807 : Fin 2886) := Fin.ext h2807
    subst k
    rw [keyMomentRowsAt2807]
    exact keyMoment2807 B hB
  · have he : k = (2808 : Fin 2886) := Fin.ext h2808
    subst k
    rw [keyMomentRowsAt2808]
    exact keyMoment2808 B hB
  · have he : k = (2809 : Fin 2886) := Fin.ext h2809
    subst k
    rw [keyMomentRowsAt2809]
    exact keyMoment2809 B hB
  · have he : k = (2810 : Fin 2886) := Fin.ext h2810
    subst k
    rw [keyMomentRowsAt2810]
    exact keyMoment2810 B hB
  · have he : k = (2811 : Fin 2886) := Fin.ext h2811
    subst k
    rw [keyMomentRowsAt2811]
    exact keyMoment2811 B hB
  · have he : k = (2812 : Fin 2886) := Fin.ext h2812
    subst k
    rw [keyMomentRowsAt2812]
    exact keyMoment2812 B hB
  · have he : k = (2813 : Fin 2886) := Fin.ext h2813
    subst k
    rw [keyMomentRowsAt2813]
    exact keyMoment2813 B hB
  · have he : k = (2814 : Fin 2886) := Fin.ext h2814
    subst k
    rw [keyMomentRowsAt2814]
    exact keyMoment2814 B hB
  · have he : k = (2815 : Fin 2886) := Fin.ext h2815
    subst k
    rw [keyMomentRowsAt2815]
    exact keyMoment2815 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
