import OAI.Analysis.LipschitzHilbert.Trees.BoundaryTelescoping
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! The exact average of the boundary-depth envelope used after telescoping. -/

noncomputable section

open MeasureTheory Set

namespace LipschitzHilbert

def geometricBoundaryLayer (ε q : ℝ) (j : ℕ) : ℝ → ℝ :=
  (Ioo 0 (ε * q ^ j)).indicator (fun _ => 1)

def geometricBoundaryDepth (ε q b : ℝ) : ℝ :=
  ∑' j : ℕ, geometricBoundaryLayer ε q j b

theorem geometricBoundaryLayer_nonneg (ε q : ℝ) (j : ℕ) (b : ℝ) :
    0 ≤ geometricBoundaryLayer ε q j b := by
  exact indicator_nonneg (fun _ _ => zero_le_one) b

theorem geometricBoundaryLayer_integrable (ε q : ℝ) (j : ℕ) :
    Integrable (geometricBoundaryLayer ε q j) := by
  exact (integrable_indicator_iff measurableSet_Ioo).2
    (integrableOn_const (by simp [Real.volume_Ioo]))

theorem integral_geometricBoundaryLayer {ε q : ℝ} (hε : 0 ≤ ε) (hq : 0 ≤ q) (j : ℕ) :
    (∫ b, geometricBoundaryLayer ε q j b) = ε * q ^ j := by
  change (∫ b, (Ioo 0 (ε * q ^ j)).indicator (1 : ℝ → ℝ) b) = _
  rw [integral_indicator_one measurableSet_Ioo,
    Real.volume_real_Ioo_of_le (by positivity), sub_zero]

theorem integral_norm_geometricBoundaryLayer {ε q : ℝ} (hε : 0 ≤ ε) (hq : 0 ≤ q) (j : ℕ) :
    (∫ b, ‖geometricBoundaryLayer ε q j b‖) = ε * q ^ j := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (geometricBoundaryLayer_nonneg ε q j _)] using
    integral_geometricBoundaryLayer hε hq j

/-- The boundary-depth average is finite and has the exact geometric-series
value. This avoids any loss depending on the number of angular levels. -/
theorem integral_geometricBoundaryDepth {ε q : ℝ}
    (hε : 0 ≤ ε) (hq : 0 ≤ q) (hq1 : q < 1) :
    (∫ b, geometricBoundaryDepth ε q b) = ε / (1 - q) := by
  have hs : Summable (fun j : ℕ => ∫ b, ‖geometricBoundaryLayer ε q j b‖) := by
    simp_rw [integral_norm_geometricBoundaryLayer hε hq]
    exact (summable_geometric_of_lt_one hq hq1).mul_left ε
  change (∫ b, ∑' j : ℕ, geometricBoundaryLayer ε q j b) = _
  rw [← integral_tsum_of_summable_integral_norm
    (geometricBoundaryLayer_integrable ε q) hs]
  simp_rw [integral_geometricBoundaryLayer hε hq]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1, div_eq_mul_inv]

theorem geometricBoundaryDepth_integrable {ε q : ℝ}
    (hε : 0 < ε) (hq : 0 ≤ q) (hq1 : q < 1) :
    Integrable (geometricBoundaryDepth ε q) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_geometricBoundaryDepth hε.le hq hq1]
  exact (div_pos hε (sub_pos.mpr hq1)).ne'

/-- With angular branching at least two, the average depth costs at most
`2ε`, independent of the depth of the hierarchy. -/
theorem integral_geometricBoundaryDepth_le {ε G : ℝ} (hε : 0 ≤ ε) (hG : 2 ≤ G) :
    (∫ b, geometricBoundaryDepth ε G⁻¹ b) ≤ 2 * ε := by
  have hG0 : 0 < G := by linarith
  have hi0 : 0 ≤ G⁻¹ := inv_nonneg.mpr hG0.le
  have hi2 : G⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using (inv_le_inv₀ hG0 (by norm_num : (0 : ℝ) < 2)).2 hG
  rw [integral_geometricBoundaryDepth hε hi0 (by linarith)]
  apply (div_le_iff₀ (by linarith : 0 < 1 - G⁻¹)).2
  nlinarith [mul_le_mul_of_nonneg_left hi2 hε]

end LipschitzHilbert

end

end OAI
