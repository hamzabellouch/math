import OAI.NumberTheory.CubicMoment.Estimates.IdealDirichletInverse
import OAI.NumberTheory.CubicMoment.Estimates.HeckeStripGrowth

namespace OAI

/-! Uniform normalization of the complete ideal series on Re(s) ≥ 2.
The lower bound follows from its actual Möbius inverse. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def idealZetaTwo : ℝ :=
  ∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))

lemma idealZetaTwo_ge_one : 1 ≤ idealZetaTwo := by
  have h := (summable_ideal_norm_rpow (by norm_num : (1:ℝ) < 2)).le_tsum
    0 (fun ν _ => Real.rpow_nonneg (idealExponentNorm_pos ν).le _)
  simpa [idealZetaTwo,idealExponentNorm,idealExponentGenerator] using h

lemma idealZetaTwo_pos : 0 < idealZetaTwo := zero_lt_one.trans_le idealZetaTwo_ge_one

lemma idealMoebius_character_norm (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (ν : EisensteinIdealExponent) :
    ‖((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)*χ ν‖ ≤ 1 := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_of_le_one_right (abs_nonneg _) (hχ ν)).trans
    (idealMoebiusSeries_abs_le_one ν)

theorem idealDirichlet_upper_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖normDirichletSeries χ idealExponentNorm s‖ ≤ idealZetaTwo :=
  norm_idealDirichlet_le_zeta_two χ hχ s hs

theorem idealDirichlet_inverse_lower_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 2 ≤ s.re) :
    1 ≤ idealZetaTwo*‖normDirichletSeries χ idealExponentNorm s‖ := by
  have he := congrArg (fun z : ℂ => ‖z‖) (idealDirichlet_moebius_mul χ hχ hχ0 hχadd
    (show 1 < s.re by linarith))
  rw [norm_mul,norm_one] at he
  rw [←he]
  exact mul_le_mul_of_nonneg_right
    (idealDirichlet_upper_bound _ (idealMoebius_character_norm χ hχ) hs)
    (_root_.norm_nonneg _)

theorem idealDirichlet_lower_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 2 ≤ s.re) :
    idealZetaTwo⁻¹ ≤ ‖normDirichletSeries χ idealExponentNorm s‖ := by
  rw [inv_eq_one_div,div_le_iff₀ idealZetaTwo_pos,mul_comm]
  exact idealDirichlet_inverse_lower_bound χ hχ hχ0 hχadd hs

theorem idealDirichlet_reciprocal_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖(normDirichletSeries χ idealExponentNorm s)⁻¹‖ ≤ idealZetaTwo := by
  rw [norm_inv,inv_eq_one_div,div_le_iff₀ (norm_pos_iff.mpr
    (idealDirichlet_ne_zero χ hχ hχ0 hχadd (show 1 < s.re by linarith)))]
  simpa only [mul_comm] using idealDirichlet_inverse_lower_bound χ hχ hχ0 hχadd hs

end CubicFirstMoment

end

end OAI
