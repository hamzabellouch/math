import OAI.Geometry.NodalSets.Charts.ChartedEnvelope
import OAI.Geometry.NodalSets.Charts.MetricCoercivity

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma coercive_vector_residual (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    {c E : ℝ} (hc : 0 < c) (hg : ∀ v, c*‖v‖^2 ≤ g v v)
    (w : Coord) (hres : ∀ v, |g w v| ≤ E*‖v‖) :
    ‖w‖ ≤ E/c := by
  by_cases hw : w = 0
  · have hE : 0 ≤ E := by
      have h := hres (Pi.single 0 1)
      simp only [hw,map_zero,zero_apply,abs_zero] at h
      simpa using h
    simp only [hw,norm_zero]
    exact div_nonneg hE hc.le
  have hn := norm_pos_iff.mpr hw
  have h := (hg w).trans ((le_abs_self _).trans (hres w))
  apply (le_div_iff₀ hc).mpr
  nlinarith

lemma metricGradient_residual_bound
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    (x q : Coord) {c E : ℝ} (hc : 0 < c)
    (hg : ∀ v, c*‖v‖^2 ≤ g x v v)
    (hres : ∀ v, |fderiv ℝ S x v-g x q v| ≤ E*‖v‖) :
    ‖metricGradient g S x-q‖ ≤ E/c := by
  have hp : ∀ v, v ≠ 0 → 0 < g x v v := by
    intro v hv
    exact (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hg v)
  apply coercive_vector_residual (g x) hc hg
  intro v
  simpa only [map_sub,sub_apply,metricGradient_pair g S x hp v] using hres v

lemma metricGradient_frozen_residual_bound
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    (x y q : Coord) {c E A R K : ℝ} (hc : 0 < c)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hg : ∀ v, c*‖v‖^2 ≤ g x v v)
    (hfreeze : ‖g x-g y‖ ≤ A*R) (hq : ‖q‖ ≤ K)
    (hres : ∀ v, |fderiv ℝ S x v-g y q v| ≤ E*‖v‖) :
    ‖metricGradient g S x-q‖ ≤ (E+A*R*K)/c := by
  apply metricGradient_residual_bound g S x q hc hg
  intro v
  have hm : |g x q v-g y q v| ≤ A*R*K*‖v‖ := by
    calc
      _ = |(g x-g y) q v| := rfl
      _ ≤ ‖g x-g y‖*‖q‖*‖v‖ := bilinear_pairing_bound _ q v
      _ ≤ A*R*K*‖v‖ :=
        mul_le_mul (mul_le_mul_of_nonneg hfreeze hq (norm_nonneg (g x-g y)) hK) le_rfl
          (norm_nonneg v) (mul_nonneg (mul_nonneg hA hR) hK)
  calc
    _ ≤ |fderiv ℝ S x v-g y q v|+|g y q v-g x q v| := abs_sub_le _ _ _
    _ ≤ E*‖v‖+A*R*K*‖v‖ := add_le_add (hres v) (by simpa [abs_sub_comm] using hm)
    _ = _ := by ring

end
end Yau.Geometry

end OAI
