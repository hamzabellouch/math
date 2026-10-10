import OAI.NumberTheory.TwoPointCorrelations.MRTCountWindows
import OAI.NumberTheory.TwoPointCorrelations.MRTTypicalCoarse

namespace OAI

/-! Exact remaining-band inclusion--exclusion inside the fixed-window
cofactor. The resulting pointwise bound keeps its finite `2^#J` cost
explicit. No estimate for the typical polynomial is assumed. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrtTypicalCoefficient_expansion {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (n : ℕ) :
    mrtTypicalCoefficient J P F n =
      ∑ I ∈ J.powerset, (-1 : ℂ) ^ I.card *
        mrtMissingCoefficient F (I.biUnion P) n := by
  have he := congrArg (fun r : ℝ => (r : ℂ))
    (mrtTypical_inclusion_exclusion J P n)
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_one] at he
  calc
    _ = F n * (∑ I ∈ J.powerset, (-1 : ℂ) ^ I.card *
        (mrtPrimeMask (I.biUnion P) n : ℂ)) := by
      rw [he]
      by_cases h : mrtTypical J P n <;>
        simp [mrtTypicalCoefficient, h]
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro I _
      unfold mrtMissingCoefficient
      ring

lemma mrt_typical_cofactor_expansion {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (Q : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) (a t : ℝ) :
    mrtCofactorPolynomial Q (mrtTypicalCoefficient J P F) N a t =
      ∑ I ∈ J.powerset, (-1 : ℂ) ^ I.card *
        mrtCofactorPolynomial Q (mrtMissingCoefficient F (I.biUnion P)) N a t := by
  unfold mrtCofactorPolynomial
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  by_cases hc : (N : ℝ) < a * n ∧ a * n ≤ 2 * N
  · simp only [ite_eq_left hc]
    unfold mrtDirichletAtom
    rw [mrtTypicalCoefficient_expansion]
    simp only [sum_mul, sum_div]
    apply sum_congr rfl
    intro I _
    ring
  · simp only [ite_eq_right hc, mul_zero, sum_const_zero]

/-- Applying the proved general Halász estimate to every actual missing-band
cofactor. This version is intended for frequencies far from a minimizing
twist; the near-twist Euler argument separately avoids the power-of-two loss. -/
theorem mrt_typical_cofactor_window_bound :
    ∃ C K X₀ : ℝ, 0 < C ∧ 0 ≤ K ∧
    ∀ (N : ℕ) (a : ℝ), 1 ≤ a → X₀ ≤ (⌊(N : ℝ) / a⌋₊ : ℝ) →
    ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
    ∀ (ι : Type*) (J : Finset ι) (P : ι → Finset ℕ) (Q : Finset ℕ),
      (∀ j ∈ J, ∀ p ∈ P j, p.Prime) → (∀ p ∈ Q, p.Prime) →
    ∀ (t T M : ℝ), 0 ≤ M →
      |t| + Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ) ^ 8 ≤ T →
      (∀ v : ℝ, |v| ≤ T →
        2 * M + K ≤ squaredDistance F (mrtArchimedeanTwist v) ⌊(2 * N : ℝ) / a⌋₊) →
      ‖mrtCofactorPolynomial Q (mrtTypicalCoefficient J P F) N a t‖ ≤
        (2 : ℝ) ^ J.card * C * ((M + 1) * Real.exp (-M) +
          Real.log (Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) /
            Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) := by
  obtain ⟨C, K, X₀, hC, hK, hb⟩ := mrt_reciprocal_count_window_bound
  refine ⟨C, K, X₀, hC, hK, ?_⟩
  intro N a ha hN F hF1 hFm hFb ι J P Q hP hQ t T M hM hT hd
  rw [mrt_typical_cofactor_expansion]
  calc
    _ ≤ ∑ I ∈ J.powerset,
        ‖(-1 : ℂ) ^ I.card *
          mrtCofactorPolynomial Q (mrtMissingCoefficient F (I.biUnion P)) N a t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ I ∈ J.powerset, C * ((M + 1) * Real.exp (-M) +
        Real.log (Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) /
          Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) := by
      apply sum_le_sum
      intro I hI
      rw [norm_mul, norm_pow]
      simp only [norm_neg, norm_one, one_pow, one_mul]
      apply hb N a ha hN F hF1 hFm hFb (I.biUnion P) Q _ hQ t T M hM hT hd
      intro p hp
      obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hp
      exact hP j ((mem_powerset.mp hI) hj) p hpj
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, card_powerset, Nat.cast_pow, Nat.cast_ofNat]
      ring

end TwoPointCorrelations

end OAI
