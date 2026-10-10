import OAI.NumberTheory.Ostmann.ZeroDensity.DensityVerticalPolynomial

namespace OAI

/-! # The mean square of the actual critical-line Möbius polynomial -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem densityMollifier_vertical {q : ℕ} (X : ℕ) (χ : DirichletCharacter ℂ q) (σ t : ℝ) :
    densityMollifier X χ (densityVerticalPoint σ t) =
      ∑ n ∈ Finset.Icc 1 X,
        densityVerticalCoeff (fun n => (ArithmeticFunction.moebius n : ℂ)) σ n *
          χ (n : ZMod q) * realAdditivePhase (-(Real.log n * t)) := by
  unfold densityMollifier
  apply Finset.sum_congr rfl
  intro n hn
  rw [density_vertical_term _ σ t n (Finset.mem_Icc.mp hn).1]
  unfold densityVerticalCoeff
  ring

 theorem density_mobius_half_energy (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
      ‖densityVerticalCoeff (fun n => (ArithmeticFunction.moebius n : ℂ)) (1 / 2) n‖ ^ 2) ≤
        1 + Real.log X := by
  have hsum : (∑ n ∈ Finset.Icc 1 X,
      ‖densityVerticalCoeff (fun n => (ArithmeticFunction.moebius n : ℂ)) (1 / 2) n‖ ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 X, (n : ℝ)⁻¹ := by
    apply Finset.sum_le_sum
    intro n hn
    rw [densityVerticalCoeff_half_square _ n (Finset.mem_Icc.mp hn).1]
    have hm : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      norm_cast
      exact ArithmeticFunction.abs_moebius_le_one
    have hsq : ‖(ArithmeticFunction.moebius n : ℂ)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (ArithmeticFunction.moebius n : ℂ)]
    simpa only [one_div] using div_le_div_of_nonneg_right hsq (Nat.cast_nonneg n)
  apply hsum.trans
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    using harmonic_le_one_add_log X

 theorem critical_mollifier_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ F : (q : ℕ) → Finset (DirichletCharacter ℂ q),
      (∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) →
      (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
        ∫ t in Icc (-T) T, ‖densityMollifier X χ (densityVerticalPoint (1 / 2) t)‖ ^ 2) ≤
          C * ((X : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log X) := by
  obtain ⟨C, hC, hmean⟩ := hybrid_multiplicative_large_sieve
  refine ⟨C, hC, ?_⟩
  intro X Q hQ T hT F hF
  have h := hmean X Q hQ T hT
    (densityVerticalCoeff (fun n => (ArithmeticFunction.moebius n : ℂ)) (1 / 2)) F hF
  simp only [← densityMollifier_vertical] at h
  exact h.trans (mul_le_mul_of_nonneg_left (density_mobius_half_energy X) (by positivity))

 theorem density_divisor_half_energy (N : ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ n.divisors.card) :
    (∑ n ∈ Finset.Icc 1 N, ‖densityVerticalCoeff a (1 / 2) n‖ ^ 2) ≤
      (1 + Real.log N) ^ 4 := by
  apply (Finset.sum_le_sum (fun n hn => ?_)).trans (density_divisor_square_harmonic N)
  rw [densityVerticalCoeff_half_square _ n (Finset.mem_Icc.mp hn).1]
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (ha n hn) 2) (Nat.cast_nonneg n)

end Ostmann

end OAI
