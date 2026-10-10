import OAI.Analysis.LipschitzHilbert.Phase.FourthMoment
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace OAI

/-!
# Analytic families for the finite Fourier interpolation

The magnitude interpolation in §7 keeps each complex phase fixed. Zero
coefficients remain zero. The identities below give exact unit boundary
norms for the coefficient and simple-test-function families.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

def magnitudeFamily (w : ℂ) (A B : ℝ) (z : ℂ) : ℂ :=
  if w = 0 then 0 else
    (w / (‖w‖ : ℂ)) * (‖w‖ : ℂ) ^ ((1 - z) * (A : ℂ) + z * (B : ℂ))

@[simp] theorem magnitudeFamily_zero (A B : ℝ) (z : ℂ) : magnitudeFamily 0 A B z = 0 := by
  simp [magnitudeFamily]

theorem norm_magnitudeFamily_of_ne_zero {w : ℂ} (hw : w ≠ 0) (A B : ℝ) (z : ℂ) :
    ‖magnitudeFamily w A B z‖ = ‖w‖ ^ ((1 - z.re) * A + z.re * B) := by
  have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hphase : ‖w / (‖w‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self hnorm]
  simp only [magnitudeFamily, hw, ite_false]
  rw [norm_mul, hphase, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hw)]
  congr 1
  simp [Complex.mul_re]

theorem norm_magnitudeFamily_left (w : ℂ) {A : ℝ} (hA : 0 < A) (B : ℝ)
    {z : ℂ} (hz : z.re = 0) : ‖magnitudeFamily w A B z‖ = ‖w‖ ^ A := by
  by_cases hw : w = 0
  · simp [hw, Real.zero_rpow hA.ne']
  · rw [norm_magnitudeFamily_of_ne_zero hw]
    simp [hz]

theorem norm_magnitudeFamily_right (w : ℂ) (A : ℝ) {B : ℝ} (hB : 0 < B)
    {z : ℂ} (hz : z.re = 1) : ‖magnitudeFamily w A B z‖ = ‖w‖ ^ B := by
  by_cases hw : w = 0
  · simp [hw, Real.zero_rpow hB.ne']
  · rw [norm_magnitudeFamily_of_ne_zero hw]
    simp [hz]

theorem magnitudeFamily_at_real (w : ℂ) (A B t : ℝ)
    (ht : (1 - t) * A + t * B = 1) : magnitudeFamily w A B (t : ℂ) = w := by
  by_cases hw : w = 0
  · simp [hw]
  · have he : (1 - (t : ℂ)) * (A : ℂ) + (t : ℂ) * (B : ℂ) = 1 := by
      exact_mod_cast ht
    simp only [magnitudeFamily, hw, ite_false]
    rw [he, Complex.cpow_one]
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw))

theorem differentiable_magnitudeFamily (w : ℂ) (A B : ℝ) :
    Differentiable ℂ (magnitudeFamily w A B) := by
  by_cases hw : w = 0
  · change Differentiable ℂ (fun z => magnitudeFamily w A B z)
    simp only [hw, magnitudeFamily_zero]
    exact differentiable_const (0 : ℂ)
  · have hf : Differentiable ℂ (fun z : ℂ => (1 - z) * (A : ℂ) + z * (B : ℂ)) := by
      fun_prop
    have hn : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
    change Differentiable ℂ (fun z => magnitudeFamily w A B z)
    simp only [magnitudeFamily, hw, ite_false]
    exact (differentiable_const (w / (‖w‖ : ℂ))).mul (hf.const_cpow (Or.inl hn))

theorem norm_magnitudeFamily_le (w : ℂ) (A B : ℝ) {z : ℂ}
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖magnitudeFamily w A B z‖ ≤ ‖w‖ ^ min A B + ‖w‖ ^ max A B := by
  by_cases hw : w = 0
  · rw [hw, magnitudeFamily_zero, norm_zero]
    positivity
  · rw [norm_magnitudeFamily_of_ne_zero hw]
    have hlo : min A B ≤ (1 - z.re) * A + z.re * B := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (min_le_left A B)) (sub_nonneg.mpr hz1),
        mul_nonneg (sub_nonneg.mpr (min_le_right A B)) hz0]
    have hhi : (1 - z.re) * A + z.re * B ≤ max A B := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_max_left A B)) (sub_nonneg.mpr hz1),
        mul_nonneg (sub_nonneg.mpr (le_max_right A B)) hz0]
    by_cases hnorm : 1 ≤ ‖w‖
    · exact (Real.rpow_le_rpow_of_exponent_le hnorm hhi).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _))
    · exact (Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.mpr hw)
        (le_of_not_ge hnorm) hlo).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))

variable {ι : Type*} [Fintype ι]

def coefficientFamily (a : ι → ℂ) (r p₀ p₁ : ℝ) (z : ℂ) (i : ι) : ℂ :=
  magnitudeFamily (a i) (r / p₀) (r / p₁) z

omit [Fintype ι] in
theorem coefficientFamily_at_real (a : ι → ℂ) (r p₀ p₁ t : ℝ)
    (ht : (1 - t) * (r / p₀) + t * (r / p₁) = 1) :
    coefficientFamily a r p₀ p₁ (t : ℂ) = a := by
  funext i
  exact magnitudeFamily_at_real (a i) _ _ t ht

theorem coefficientFamily_left_power_sum (a : ι → ℂ) {r p₀ p₁ : ℝ}
    (hr : 0 < r) (hp₀ : 0 < p₀) {z : ℂ} (hz : z.re = 0) :
    (∑ i, ‖coefficientFamily a r p₀ p₁ z i‖ ^ p₀) = ∑ i, ‖a i‖ ^ r := by
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficientFamily, norm_magnitudeFamily_left (a i) (div_pos hr hp₀) _ hz,
    ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  field_simp

theorem coefficientFamily_right_power_sum (a : ι → ℂ) {r p₀ p₁ : ℝ}
    (hr : 0 < r) (hp₁ : 0 < p₁) {z : ℂ} (hz : z.re = 1) :
    (∑ i, ‖coefficientFamily a r p₀ p₁ z i‖ ^ p₁) = ∑ i, ‖a i‖ ^ r := by
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficientFamily, norm_magnitudeFamily_right (a i) _ (div_pos hr hp₁) hz,
    ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  field_simp

theorem weighted_magnitudeFamily_left_power_sum (w : ι → ℝ) (a : ι → ℂ) {r p₀ p₁ : ℝ}
    (hr : 0 < r) (hp₀ : 0 < p₀) {z : ℂ} (hz : z.re = 0) :
    (∑ i, w i * ‖coefficientFamily a r p₀ p₁ z i‖ ^ p₀) = ∑ i, w i * ‖a i‖ ^ r := by
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficientFamily, norm_magnitudeFamily_left (a i) (div_pos hr hp₀) _ hz,
    ← Real.rpow_mul (norm_nonneg _)]
  congr 2
  field_simp

theorem weighted_magnitudeFamily_right_power_sum (w : ι → ℝ) (a : ι → ℂ) {r p₀ p₁ : ℝ}
    (hr : 0 < r) (hp₁ : 0 < p₁) {z : ℂ} (hz : z.re = 1) :
    (∑ i, w i * ‖coefficientFamily a r p₀ p₁ z i‖ ^ p₁) = ∑ i, w i * ‖a i‖ ^ r := by
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficientFamily, norm_magnitudeFamily_right (a i) _ (div_pos hr hp₁) hz,
    ← Real.rpow_mul (norm_nonneg _)]
  congr 2
  field_simp

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
