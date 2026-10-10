import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

namespace OAI

namespace Ostmann

open MeasureTheory
open scoped RealInnerProductSpace

theorem abs_two_inner_le_weighted_sq (z w : ℂ) {c : ℝ} (hc : 0 < c) :
    |2 * inner ℝ z w| ≤ c * ‖z‖ ^ 2 + c⁻¹ * ‖w‖ ^ 2 := by
  have hcs := abs_real_inner_le_norm z w
  have hs := sq_nonneg (c * ‖z‖ - ‖w‖)
  have hi : c * c⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hc)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (mul_le_mul_of_nonneg_left hcs (by norm_num : (0 : ℝ) ≤ 2)).trans
  apply (mul_le_mul_iff_right₀ hc).mp
  nlinarith

theorem integral_abs_two_inner_le_energy
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c) :
    (∫ t in a..b, |2 * inner ℝ (f t) (g t)|) ≤
      c * (∫ t in a..b, ‖f t‖ ^ 2) + c⁻¹ * (∫ t in a..b, ‖g t‖ ^ 2) := by
  have hF : Continuous (fun t => ‖f t‖ ^ 2) := hf.norm.pow 2
  have hG : Continuous (fun t => ‖g t‖ ^ 2) := hg.norm.pow 2
  calc
    (∫ t in a..b, |2 * inner ℝ (f t) (g t)|) ≤
        ∫ t in a..b, c * ‖f t‖ ^ 2 + c⁻¹ * ‖g t‖ ^ 2 := by
      apply intervalIntegral.integral_mono hab
      · exact ((hf.inner hg).const_mul 2).abs.intervalIntegrable _ _
      · exact ((hF.const_mul c).add (hG.const_mul c⁻¹)).intervalIntegrable _ _
      · intro t
        exact abs_two_inner_le_weighted_sq (f t) (g t) hc
    _ = _ := by
      rw [intervalIntegral.integral_add ((hF.const_mul c).intervalIntegrable _ _)
        ((hG.const_mul c⁻¹).intervalIntegrable _ _)]
      simp only [intervalIntegral.integral_const_mul]

theorem sampling_energy_algebra {D E L δ c : ℝ} (hδ : 0 < δ)
    (hc : 0 < c) (hE : 0 ≤ E) (hL : L ≤ c ^ 2 * (2 * E))
    (hD : δ * D ≤ 2 * E + δ * (c * (2 * E) + c⁻¹ * L)) :
    D ≤ (2 / δ + 4 * c) * E := by
  have hic : 0 < c⁻¹ := inv_pos.mpr hc
  have hi : c * c⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hc)
  have hd : δ * (2 / δ) = 2 := by field_simp
  have hCL := mul_le_mul_of_nonneg_left hL hic.le
  have hL' : c⁻¹ * L ≤ 2 * c * E := by
    calc
      c⁻¹ * L ≤ c⁻¹ * (c ^ 2 * (2 * E)) := hCL
      _ = 2 * c * E := by field_simp
  apply (mul_le_mul_iff_right₀ hδ).mp
  nlinarith [mul_le_mul_of_nonneg_left hL' hδ.le]

end Ostmann

end OAI
