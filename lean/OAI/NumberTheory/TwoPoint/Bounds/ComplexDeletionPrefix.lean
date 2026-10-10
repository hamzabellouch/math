import OAI.NumberTheory.TwoPoint.Bounds.ComplexNumericalPrefix

namespace OAI

/-! The existing positive endpoint costs control ordinary complex prefix loss. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem complex_uncut_sub_retained_prefix_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i k, k ≠ i → Disjoint (P i) (P k))
    (R Q : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℤ → ℕ → ℕ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (bad : ℤ → ℤ → Prop) (j : ℤ) (N : ℕ)
    (F G : ℤ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 1) (hG : ∀ n, ‖G n‖ ≤ 1)
    (hsub : ∀ d ∈ primeTupleDivisors P, ∀ q ∈ R,
      eligible j d q → actualPaddingBin η (c d) j q) :
    ‖untwistedUncutPrefix P R (eligible j) h gate F G N -
      untwistedRetainedPrefix P R Q actualPaddingCoefficient (eligible j) L K W
        (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad j z) F G N‖ ≤
      (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uniformAverage (fun x : Fin N => positiveDeletionAtom (primeTuplePool P) Q R
          η c L K W eligible bad j d q ((x.val + 1 : ℕ) : ℤ))) +
      (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uniformAverage (fun x : Fin N => positiveDeletionAtom (primeTuplePool P) Q R
          η c L K W eligible bad j d q (((x.val + 1 : ℕ) : ℤ) + (h * q * d : ℕ)))) := by
  unfold untwistedUncutPrefix untwistedRetainedPrefix
  have hb (n : ℕ) :
      ‖(∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        liouvilleUntwist F G n ((n : ℤ) + (h * q * d : ℕ)) *
        uncutNumericalEdge R (eligible j) h gate d q n ((n : ℤ) + (h * q * d : ℕ))) -
        (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        liouvilleUntwist F G n ((n : ℤ) + (h * q * d : ℕ)) *
        retainedNumericalEdge P R Q actualPaddingCoefficient (eligible j) L K W
          (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad j z)
          d q n ((n : ℤ) + (h * q * d : ℕ)))‖ ≤
      ∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        (positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q n +
        positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q
          ((n : ℤ) + (h * q * d : ℕ))) := by
    simp only [← sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro d hd
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro q _
    exact complex_uncut_sub_retained_edge_le P R Q η c L K W eligible h gate bad j d q n
      (hsub d hd) (primeTupleDivisors_arithmetic P hprime hdisjoint hd).2.1 F G hF hG
  have hp := normalized_prefix_difference_le _ _ _ N hb
  apply hp.trans_eq
  have hadd (f g : Fin N → ℝ) : uniformAverage (fun x => f x + g x) =
      uniformAverage f + uniformAverage g := by
    simp only [uniformAverage, sum_add_distrib, add_div]
  simp only [uniformAverage_finset_sum, hadd, sum_add_distrib]

end TwoPointCorrelations

end OAI
