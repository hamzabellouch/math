import OAI.NumberTheory.Ostmann.Tree.PairSquareMoment

namespace OAI

/-! # Small individual and bounded total means of pair coefficients -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance pairCoefficientMeansFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem autocorrelation_energy_le_fourier_sup {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hflat : ∀ a, ‖additiveFourier f a‖ ≤ ε) :
    (∑ d : ZMod p, ‖additiveAutocorrelation f d‖ ^ 2) ≤
      ε ^ 2 * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  rw [additiveFourier_energy (additiveAutocorrelation f)]
  simp only [additiveFourier_autocorrelation, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ (p : ℝ) * ∑ a : ZMod p, ε ^ 2 * ‖additiveFourier f a‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro a _
      rw [pow_two (‖additiveFourier f a‖ ^ 2)]
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) hε).mpr (hflat a)) (sq_nonneg _)
    _ = _ := by
      rw [← Finset.mul_sum, mul_left_comm, ← additiveFourier_energy f]

theorem fieldPairCoefficientMoment_le_autocorrelation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (d : ZMod p) :
    fieldPairCoefficientMoment g χ d ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        ‖additiveAutocorrelation (characterTwist g χ) d‖ ^ 2 := by
  by_cases hd : d = 0
  · rw [hd, fieldPairCoefficientMoment_zero]
    positivity
  · let du : (ZMod p)ˣ := Units.mk0 d hd
    have he : (fun t : (ZMod p)ˣ => fieldBottomPairValue g d t) = bottomPairValue g du := by
      funext t
      simp only [fieldBottomPairValue, hd, Units.ne_zero, dite_false, Units.mk0_val, du]
    unfold fieldPairCoefficientMoment
    rw [he, bottomPair_mellin_autocorrelation]
    simp only [norm_mul, norm_div, Complex.norm_natCast, mul_pow, du, Units.val_mk0]
    exact le_rfl

theorem fieldPairCoefficientMoment_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (χ : MulChar (ZMod p) ℂ)
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : ∀ a, ‖additiveFourier (characterTwist g χ) a‖ ≤ ε)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ d : ZMod p, fieldPairCoefficientMoment g χ d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 3 * ε ^ 2 := by
  have hnorm (x : ZMod p) : ‖characterTwist g χ x‖ = ‖g x‖ := by
    by_cases hx : x = 0
    · simp [hx, characterTwist, hg]
    · have hn := norm_mulChar_unit χ (Units.mk0 x hx)
      simpa only [characterTwist, norm_mul, Complex.norm_conj, Units.val_mk0, hn, mul_one]
        using congrArg (fun t : ℝ => ‖g x‖ * t) hn
  have hauto := autocorrelation_energy_le_fourier_sup (characterTwist g χ) ε hε hflat
  simp_rw [hnorm] at hauto
  have hsum := (Finset.sum_le_sum fun d (_ : d ∈ (Finset.univ : Finset (ZMod p))) =>
    fieldPairCoefficientMoment_le_autocorrelation g χ d)
  rw [← Finset.mul_sum] at hsum
  have hU : 0 ≤ (Fintype.card (ZMod p)ˣ : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 * (ε ^ 2 * p)) /
        (Fintype.card (ZMod p)ˣ : ℝ) := by
      apply div_le_div_of_nonneg_right _ hU
      exact hsum.trans (mul_le_mul_of_nonneg_left
        (hauto.trans (mul_le_mul_of_nonneg_left henergy (sq_nonneg _))) (sq_nonneg _))
    _ = _ := by ring

theorem fieldPairCoefficientMoment_total_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ χ : MulChar (ZMod p) ℂ,
      (∑ d : ZMod p, fieldPairCoefficientMoment g χ d) /
        (Fintype.card (ZMod p)ˣ : ℝ)) ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 := by
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [sum_fieldPairCoefficientMoment]
  exact fieldPairMoment_mean_le g hg henergy

end Ostmann

end OAI
