import OAI.Analysis.IrrationalRotation.Analysis.LaurentWindow
import OAI.Analysis.IrrationalRotation.Analysis.FiniteConvolution
import OAI.Analysis.IrrationalRotation.Model.LaurentConvolution

namespace OAI

noncomputable section

namespace Invariant233.LaurentWindow

open InvariantProjection.FiniteConvolution

theorem laurent_lower_bound_of_finite_bound (K : ℕ) (D δ ε : ℝ)
    (hbound : ∀ a b : Coefficients K,
      (∀ i, ‖a i‖ ≤ D) → (∀ i, ‖b i‖ ≤ D) →
      δ ≤ ‖a (center K)‖ → δ ≤ ‖b (center K)‖ →
      ∃ n : Fin (2 * K + 1), ε ≤ ‖lowProduct a b n‖) :
    ∀ A B : LaurentPolynomial ℂ,
      (∀ i : ℤ, i < -(K : ℤ) ∨ (K : ℤ) < i → A.coeff i = 0) →
      (∀ i : ℤ, i < -(K : ℤ) ∨ (K : ℤ) < i → B.coeff i = 0) →
      (∀ i : ℤ, ‖A.coeff i‖ ≤ D) →
      (∀ i : ℤ, ‖B.coeff i‖ ≤ D) →
      δ ≤ ‖A.coeff 0‖ → δ ≤ ‖B.coeff 0‖ →
      ∃ n : ℕ, n ≤ 2 * K ∧ ε ≤ ‖(A * B).coeff (-(n : ℤ))‖ := by
  intro A B hAs hBs hA hB hA0 hB0
  let a : Coefficients K := fun i => A.coeff ((i : ℤ) - (K : ℤ))
  let b : Coefficients K := fun i => B.coeff ((i : ℤ) - (K : ℤ))
  have ha0 : δ ≤ ‖a (center K)‖ := by simpa [a, center] using hA0
  have hb0 : δ ≤ ‖b (center K)‖ := by simpa [b, center] using hB0
  obtain ⟨n, hn⟩ := hbound a b (fun i => hA _) (fun i => hB _) ha0 hb0
  have hpa : polynomial a = LaurentPolynomial.trunc
      (A * LaurentPolynomial.T (K : ℤ)) :=
    (trunc_shift_eq_fin_sum K A (fun i hi => hAs i (Or.inr hi))).symm
  have hpb : polynomial b = LaurentPolynomial.trunc
      (B * LaurentPolynomial.T (K : ℤ)) :=
    (trunc_shift_eq_fin_sum K B (fun i hi => hBs i (Or.inr hi))).symm
  have hc : lowProduct a b n = (A * B).coeff ((n : ℤ) - 2 * (K : ℤ)) := by
    unfold lowProduct
    rw [hpa, hpb]
    exact coeff_shifted_product K (n : ℕ) A B
      (fun i hi => hAs i (Or.inl hi)) (fun i hi => hBs i (Or.inl hi))
  refine ⟨2 * K - (n : ℕ), Nat.sub_le _ _, ?_⟩
  have he : -((2 * K - (n : ℕ) : ℕ) : ℤ) = (n : ℤ) - 2 * (K : ℤ) := by
    have := n.isLt
    omega
  rw [he, ← hc]
  exact hn

theorem uniform_laurent_lower_bound (K : ℕ) (D δ : ℝ) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ A B : LaurentPolynomial ℂ,
      (∀ i : ℤ, i < -(K : ℤ) ∨ (K : ℤ) < i → A.coeff i = 0) →
      (∀ i : ℤ, i < -(K : ℤ) ∨ (K : ℤ) < i → B.coeff i = 0) →
      (∀ i : ℤ, ‖A.coeff i‖ ≤ D) →
      (∀ i : ℤ, ‖B.coeff i‖ ≤ D) →
      δ ≤ ‖A.coeff 0‖ → δ ≤ ‖B.coeff 0‖ →
      ∃ n : ℕ, n ≤ 2 * K ∧ ε ≤ ‖(A * B).coeff (-(n : ℤ))‖ := by
  obtain ⟨ε, hε, hbound⟩ := uniform_lower_bound K D δ hδ
  exact ⟨ε, hε, laurent_lower_bound_of_finite_bound K D δ ε hbound⟩

end Invariant233.LaurentWindow

namespace Invariant233.FiniteWindow

open Invariant233.LaurentWindow
open InvariantProjection.FiniteConvolution

@[simp] theorem laurent_coeff (K : ℕ) (a : ℤ → ℂ) (i : ℤ) :
    (laurent K a).coeff i = if |i| ≤ (K : ℤ) then a i else 0 := by
  rw [laurent, coeff_window_sum]
  simp only [Finset.mem_Icc, abs_le]

@[simp] theorem laurent_coeff_zero (K : ℕ) (a : ℤ → ℂ) :
    (laurent K a).coeff 0 = a 0 := by
  simp only [laurent_coeff, abs_zero, Int.natCast_nonneg, ite_true]

theorem coeff_laurent_product (K : ℕ) (a b : ℤ → ℂ) (n : ℕ) :
    (laurent K a * laurent K b).coeff (-(n : ℤ)) = convolution K a b n :=
  coeff_symmetric_window_product K a b (n : ℤ)

theorem convolution_lower_bound_of_finite_bound (K : ℕ) (D δ ε : ℝ)
    (hfinite : ∀ a b : Coefficients K,
      (∀ i, ‖a i‖ ≤ D) → (∀ i, ‖b i‖ ≤ D) →
      δ ≤ ‖a (center K)‖ → δ ≤ ‖b (center K)‖ →
      ∃ n : Fin (2 * K + 1), ε ≤ ‖lowProduct a b n‖) :
    ∀ a b : ℤ → ℂ,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a i‖ ≤ D) →
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b i‖ ≤ D) →
      δ ≤ ‖a 0‖ → δ ≤ ‖b 0‖ →
      ∃ n : ℕ, n ≤ 2 * K ∧ ε ≤ ‖convolution K a b n‖ := by
  have hbound := laurent_lower_bound_of_finite_bound K D δ ε hfinite
  intro a b ha hb ha0 hb0
  have hD : 0 ≤ D := (norm_nonneg (a 0)).trans (ha 0 (by simp))
  have support_zero : ∀ c : ℤ → ℂ, ∀ i : ℤ,
      i < -(K : ℤ) ∨ (K : ℤ) < i → (laurent K c).coeff i = 0 := by
    intro c i hi
    rw [laurent_coeff, ite_eq_right]
    simp only [abs_le]
    omega
  have coeff_bound : ∀ c : ℤ → ℂ,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖c i‖ ≤ D) →
      ∀ i : ℤ, ‖(laurent K c).coeff i‖ ≤ D := by
    intro c hc i
    rw [laurent_coeff]
    split_ifs with hi
    · exact hc i hi
    · simpa only [norm_zero] using hD
  obtain ⟨n, hn, hnc⟩ := hbound (laurent K a) (laurent K b)
    (support_zero a) (support_zero b) (coeff_bound a ha) (coeff_bound b hb)
    (by simpa only [laurent_coeff_zero] using ha0)
    (by simpa only [laurent_coeff_zero] using hb0)
  exact ⟨n, hn, by simpa only [coeff_laurent_product] using hnc⟩

theorem convolution_sum_lower_bound_of_finite_bound (K : ℕ) (D δ ε : ℝ)
    (hfinite : ∀ a b : Coefficients K,
      (∀ i, ‖a i‖ ≤ D) → (∀ i, ‖b i‖ ≤ D) →
      δ ≤ ‖a (center K)‖ → δ ≤ ‖b (center K)‖ →
      ∃ n : Fin (2 * K + 1), ε ≤ ‖lowProduct a b n‖) :
    ∀ a b : ℤ → ℂ,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a i‖ ≤ D) →
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b i‖ ≤ D) →
      δ ≤ ‖a 0‖ → δ ≤ ‖b 0‖ →
      ε ≤ ∑ n ∈ Finset.range (2 * K + 1), ‖convolution K a b n‖ := by
  intro a b ha hb ha0 hb0
  obtain ⟨n, hn, hnc⟩ :=
    convolution_lower_bound_of_finite_bound K D δ ε hfinite a b ha hb ha0 hb0
  exact hnc.trans (Finset.single_le_sum (fun k hk => norm_nonneg _)
    (Finset.mem_range.mpr (by omega)))

theorem uniform_convolution_lower_bound (K : ℕ) (D δ : ℝ) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ a b : ℤ → ℂ,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a i‖ ≤ D) →
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b i‖ ≤ D) →
      δ ≤ ‖a 0‖ → δ ≤ ‖b 0‖ →
      ∃ n : ℕ, n ≤ 2 * K ∧ ε ≤ ‖convolution K a b n‖ := by
  obtain ⟨ε, hε, hbound⟩ := uniform_lower_bound K D δ hδ
  exact ⟨ε, hε, convolution_lower_bound_of_finite_bound K D δ ε hbound⟩

theorem uniform_convolution_sum_lower_bound (K : ℕ) (D δ : ℝ) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ a b : ℤ → ℂ,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a i‖ ≤ D) →
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b i‖ ≤ D) →
      δ ≤ ‖a 0‖ → δ ≤ ‖b 0‖ →
      ε ≤ ∑ n ∈ Finset.range (2 * K + 1), ‖convolution K a b n‖ := by
  obtain ⟨ε, hε, hbound⟩ := uniform_convolution_lower_bound K D δ hδ
  refine ⟨ε, hε, ?_⟩
  intro a b ha hb ha0 hb0
  obtain ⟨n, hn, hnc⟩ := hbound a b ha hb ha0 hb0
  exact hnc.trans (Finset.single_le_sum (fun k hk => norm_nonneg _)
    (Finset.mem_range.mpr (by omega)))

theorem support_laurent_coeff_subset (K : ℕ) (a : ℤ → ℂ) :
    Function.support (laurent K a).coeff ⊆ Set.Icc (-(K : ℤ)) (K : ℤ) := by
  intro i hi
  have hne := Function.mem_support.mp hi
  by_contra h
  have habs : ¬ |i| ≤ (K : ℤ) := by simpa only [abs_le, Set.mem_Icc] using h
  exact hne (by simp only [laurent_coeff, ite_eq_right habs])

theorem sum_laurent_coeff_eq_convolution (K : ℕ) (a b : ℤ → ℂ) (n : ℕ) :
    (∑ v ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      (laurent K a).coeff v * (laurent K b).coeff (-(n : ℤ) - v)) =
      convolution K a b n := by
  classical
  unfold convolution
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  have hvabs : |v| ≤ (K : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hv)
  have hneg : |-(n : ℤ) - v| = |(n : ℤ) + v| := by
    rw [show -(n : ℤ) - v = -((n : ℤ) + v) by ring, abs_neg]
  rw [laurent_coeff, ite_eq_left hvabs, laurent_coeff, hneg]
  split_ifs <;> simp

theorem convolution_sum_lower_bound_of_supported_bound (K : ℕ) (D δ ε : ℝ)
    (hsource : ∀ A B : ℤ → ℂ,
      Function.support A ⊆ Set.Icc (-(K : ℤ)) (K : ℤ) →
      Function.support B ⊆ Set.Icc (-(K : ℤ)) (K : ℤ) →
      (∀ i, ‖A i‖ ≤ D) → (∀ i, ‖B i‖ ≤ D) →
      δ ≤ ‖A 0‖ → δ ≤ ‖B 0‖ →
      ∃ n ∈ Finset.Icc 0 (2 * K), ε ≤ ‖∑ v ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        A v * B (-(n : ℤ) - v)‖) :
    ∀ a b : ℤ → ℂ,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a i‖ ≤ D) →
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b i‖ ≤ D) →
      δ ≤ ‖a 0‖ → δ ≤ ‖b 0‖ →
      ε ≤ ∑ n ∈ Finset.range (2 * K + 1), ‖convolution K a b n‖ := by
  intro a b ha hb ha0 hb0
  have hD : 0 ≤ D := (norm_nonneg (a 0)).trans (ha 0 (by simp))
  have coeff_bound : ∀ c : ℤ → ℂ,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖c i‖ ≤ D) →
      ∀ i, ‖(laurent K c).coeff i‖ ≤ D := by
    intro c hc i
    rw [laurent_coeff]
    split_ifs with hi
    · exact hc i hi
    · simpa only [norm_zero] using hD
  obtain ⟨n, hn, hc⟩ := hsource (laurent K a).coeff (laurent K b).coeff
    (support_laurent_coeff_subset K a) (support_laurent_coeff_subset K b)
    (coeff_bound a ha) (coeff_bound b hb)
    (by simpa only [laurent_coeff_zero] using ha0)
    (by simpa only [laurent_coeff_zero] using hb0)
  rw [sum_laurent_coeff_eq_convolution] at hc
  exact hc.trans (Finset.single_le_sum (fun k hk => norm_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)))

end Invariant233.FiniteWindow

end

end OAI
