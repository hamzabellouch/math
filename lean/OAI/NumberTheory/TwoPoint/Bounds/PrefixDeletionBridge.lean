import OAI.NumberTheory.TwoPoint.Walks.RetainedDeletionBridge

namespace OAI

/-! Sum the pointwise endpoint loss over the same positive prefixes as
the spectral test, retaining every tuple and padding weight. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma normalized_prefix_difference_le (F G : ℕ → ℂ) (cost : ℕ → ℝ) (N : ℕ)
    (hb : ∀ n, ‖F n - G n‖ ≤ cost n) :
    ‖positivePrefix F N / (N : ℂ) - positivePrefix G N / (N : ℂ)‖ ≤
      uniformAverage (fun x : Fin N => cost (x.val + 1)) := by
  rw [← sub_div]
  have he : positivePrefix F N - positivePrefix G N = positivePrefix (fun n => F n - G n) N := by
    simp only [positivePrefix, sum_sub_distrib]
  rw [he, norm_div, Complex.norm_natCast]
  unfold positivePrefix uniformAverage
  rw [Fintype.card_fin, Fin.sum_univ_eq_sum_range (fun x => cost (x + 1)) N]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (norm_sum_le _ _).trans (sum_le_sum (fun n _ => hb (n + 1)))

noncomputable def uncutPrimePrefix {J : ℕ} (P : Fin J → Finset ℕ)
    (R : Finset ℕ) (eligible : ℕ → ℕ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (N : ℕ) : ℂ :=
  positivePrefix (fun n => ∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
    uncutNumericalEdge R eligible h gate d q n ((n : ℤ) + (h * q * d : ℕ))) N / (N : ℂ)

theorem uncut_sub_retained_prefix_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i k, k ≠ i → Disjoint (P i) (P k))
    (R Q : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℤ → ℕ → ℕ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (bad : ℤ → ℤ → Prop) (j : ℤ) (N : ℕ)
    (hsub : ∀ d ∈ primeTupleDivisors P, ∀ q ∈ R,
      eligible j d q → actualPaddingBin η (c d) j q) :
    ‖uncutPrimePrefix P R (eligible j) h gate N -
      retainedPrimePrefix P R Q actualPaddingCoefficient (eligible j) L K W
        (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad j z) N‖ ≤
      (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uniformAverage (fun x : Fin N => positiveDeletionAtom (primeTuplePool P) Q R
          η c L K W eligible bad j d q ((x.val + 1 : ℕ) : ℤ))) +
      (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uniformAverage (fun x : Fin N => positiveDeletionAtom (primeTuplePool P) Q R
          η c L K W eligible bad j d q (((x.val + 1 : ℕ) : ℤ) + (h * q * d : ℕ)))) := by
  rw [retainedPrimePrefix_eq_numerical P hprime hdisjoint]
  unfold uncutPrimePrefix
  have hb (n : ℕ) :
      ‖(∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uncutNumericalEdge R (eligible j) h gate d q n ((n : ℤ) + (h * q * d : ℕ))) -
        (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
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
    exact uncut_sub_retained_edge_le P R Q η c L K W eligible h gate bad j d q n
      (hsub d hd) (primeTupleDivisors_arithmetic P hprime hdisjoint hd).2.1
  have hp := normalized_prefix_difference_le _ _ _ N hb
  apply hp.trans_eq
  have hadd (f g : Fin N → ℝ) : uniformAverage (fun x => f x + g x) =
      uniformAverage f + uniformAverage g := by
    simp only [uniformAverage, sum_add_distrib, add_div]
  simp only [uniformAverage_finset_sum, hadd, sum_add_distrib]

end TwoPointCorrelations

end OAI
