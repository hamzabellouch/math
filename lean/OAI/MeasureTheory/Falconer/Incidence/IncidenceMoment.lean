import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

/-! # The natural-number incidence moment used to select transverse pins -/

namespace Falconer
open MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

private theorem rpow_pow_nat (x : ℝ≥0∞) (a : ℝ) (k : ℕ) :
    (x^a)^k = x^(a*k) := by
  rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]

theorem incidence_moment (μ : Measure X) (F : X → ℝ≥0∞) (hF : AEMeasurable F μ)
    {k : ℕ} (hk : 2 ≤ k) :
    (∫⁻ x, F x ∂μ)^k ≤ (∫⁻ x, (F x)^k ∂μ)*(μ Set.univ)^(k-1) := by
  have hk' : 1 < (k:ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hk0 : (k:ℝ) ≠ 0 := by linarith
  have hkm0 : (k:ℝ)-1 ≠ 0 := by linarith
  have hc : (k:ℝ).HolderConjugate ((k:ℝ)/((k:ℝ)-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hk').mpr rfl
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc hF
    (aemeasurable_const : AEMeasurable (fun _ : X => (1:ℝ≥0∞)) μ)
  simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_one,
    ENNReal.rpow_natCast] at hH
  have hp := pow_le_pow_left' hH k
  apply hp.trans_eq
  rw [mul_pow,rpow_pow_nat,rpow_pow_nat]
  have hfirst : (1/(k:ℝ))*(k:ℝ) = 1 := by field_simp
  have hsecond : (1/((k:ℝ)/((k:ℝ)-1)))*(k:ℝ) = ((k-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k),Nat.cast_one]
    field_simp
  rw [hfirst,hsecond,ENNReal.rpow_one,ENNReal.rpow_natCast]

end Falconer

end OAI
