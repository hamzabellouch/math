import OAI.NumberTheory.Ostmann.Construction.PositiveWordBins
import OAI.NumberTheory.Ostmann.Construction.ComplexCellMeans
import OAI.NumberTheory.Ostmann.Arithmetic.ScaledPoisson

namespace OAI

/-! # The initial nonnegative word statistic -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def wordStatisticTerm {m : ℕ} (ψ : 𝓢(ℝ, ℂ)) (X : ℝ)
    (G : ℤ → ℂ) (R : Fin m → ℤ → ℂ) (a : ℤ) : ℝ :=
  (ψ ((a : ℝ) / X)).re * ‖G a‖ ^ 2 * ∏ i, ‖R i a‖ ^ 2

theorem wordStatisticTerm_nonneg {m : ℕ} (ψ : 𝓢(ℝ, ℂ)) (X : ℝ)
    (G : ℤ → ℂ) (R : Fin m → ℤ → ℂ) (hψ : ∀ x, 0 ≤ (ψ x).re) (a : ℤ) :
    0 ≤ wordStatisticTerm ψ X G R a := by
  unfold wordStatisticTerm
  have hψa := hψ ((a : ℝ) / X)
  positivity

theorem wordStatisticTerm_summable {m : ℕ} (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (G : ℤ → ℂ) (R : Fin m → ℤ → ℂ) (hψ : ∀ x, 0 ≤ (ψ x).re)
    (hG : ∀ a, ‖G a‖ ≤ 1) (hR : ∀ i a, ‖R i a‖ ≤ 1) :
    Summable (wordStatisticTerm ψ X G R) := by
  have hsum : Summable (fun a : ℤ => ‖ψ ((a : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  apply Summable.of_norm_bounded hsum
  intro a
  rw [Real.norm_eq_abs, abs_of_nonneg (wordStatisticTerm_nonneg ψ X G R hψ a)]
  have hg : ‖G a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (G a), hG a]
  have hr : (∏ i, ‖R i a‖ ^ 2) ≤ 1 := Finset.prod_le_one₀
    (fun i _ => sq_nonneg _) (fun i _ => by nlinarith [norm_nonneg (R i a), hR i a])
  calc
    wordStatisticTerm ψ X G R a ≤ (ψ ((a : ℝ) / X)).re := by
      unfold wordStatisticTerm
      exact (mul_le_of_le_one_right (mul_nonneg (hψ _) (sq_nonneg _)) hr).trans
        (mul_le_of_le_one_right (hψ _) hg)
    _ ≤ ‖ψ ((a : ℝ) / X)‖ := Complex.re_le_norm _

/-- The selected endpoints give a lower bound for the full positive
statistic, with all cell multiplicities retained. -/
theorem wordStatistic_lower {m : ℕ} (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (G : ℤ → ℂ) (R : Fin m → ℤ → ℂ) (S : Finset ℤ)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hG : ∀ a, ‖G a‖ ≤ 1) (hR : ∀ i a, ‖R i a‖ ≤ 1)
    (c u δ : ℝ) (hu : 0 ≤ u) (hδ : 0 ≤ δ)
    (hcS : ∀ a ∈ S, c ≤ (ψ ((a : ℝ) / X)).re)
    (huS : ∀ a ∈ S, u ≤ ‖G a‖) (hδS : ∀ a ∈ S, ∀ i, δ ≤ ‖R i a‖) :
    S.card * (c * u ^ 2 * δ ^ (2 * m)) ≤ ∑' a : ℤ, wordStatisticTerm ψ X G R a := by
  have hpoint : ∀ a ∈ S, c * u ^ 2 * δ ^ (2 * m) ≤ wordStatisticTerm ψ X G R a := by
    intro a ha
    have hψa := hψ ((a : ℝ) / X)
    have hg : u ^ 2 ≤ ‖G a‖ ^ 2 := pow_le_pow_left₀ hu (huS a ha) _
    have hr : δ ^ (2 * m) ≤ ∏ i, ‖R i a‖ ^ 2 := by
      rw [pow_mul]
      calc
        (δ ^ 2) ^ m = ∏ _i : Fin m, δ ^ 2 := by simp
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
          (fun i _ => pow_le_pow_left₀ hδ (hδS a ha i) _)
    exact mul_le_mul (mul_le_mul (hcS a ha) hg (sq_nonneg _) (hψ _)) hr
      (by positivity) (by positivity)
  have hfinite := Finset.sum_le_sum hpoint
  simp only [Finset.sum_const, nsmul_eq_mul] at hfinite
  exact hfinite.trans ((wordStatisticTerm_summable ψ X hX G R hψ hG hR).sum_le_tsum S
    (fun a _ => wordStatisticTerm_nonneg ψ X G R hψ a))

end Ostmann

end OAI
