import OAI.Geometry.RCD.Transport.HyperbolicChord
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! # The flat limit of the hyperbolic chord -/

open Set Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem tendsto_sinh_ratio_zero (a : ℝ) :
    Tendsto (fun q : ℝ => Real.sinh (a*q)/Real.sinh q) (𝓝[≠] 0) (𝓝 a) := by
  have ha : HasDerivAt (fun q : ℝ => Real.sinh (a*q)) a 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul a).sinh
  have h₁ : Tendsto (fun q : ℝ => Real.sinh (a*q)/q) (𝓝[≠] 0) (𝓝 a) := by
    simpa [slope_fun_def_field] using ha.tendsto_slope
  have h₂ : Tendsto (fun q : ℝ => Real.sinh q/q) (𝓝[≠] 0) (𝓝 (1:ℝ)) := by
    simpa [slope_fun_def_field] using (Real.hasDerivAt_sinh 0).tendsto_slope
  have hh := h₁.div h₂ (by norm_num)
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq0 : q ≠ 0 := hq
  simp only [Pi.div_apply]
  field_simp [hq0, Real.sinh_ne_zero.mpr hq0]

theorem tendsto_hyperbolicChord_zero (A B t : ℝ) :
    Tendsto (fun q : ℝ => hyperbolicChord q A B t) (𝓝[≠] 0)
      (𝓝 ((1-t)*A+t*B)) := by
  have hh := ((tendsto_sinh_ratio_zero (1-t)).mul_const A).add
    ((tendsto_sinh_ratio_zero t).mul_const B)
  convert hh using 1
  ext q
  simp only [hyperbolicChord, mul_comm q]
  ring

theorem continuousAt_hyperbolicChord_parameter {q : ℝ} (hq : 0 < q) (A B t : ℝ) :
    ContinuousAt (fun q : ℝ => hyperbolicChord q A B t) q := by
  unfold hyperbolicChord
  exact (((Real.continuous_sinh.comp (continuous_id.mul_const (1-t))).mul_const A).add
    ((Real.continuous_sinh.comp (continuous_id.mul_const t)).mul_const B)).continuousAt.div
      Real.continuous_sinh.continuousAt (Real.sinh_pos_iff.mpr hq).ne'

end RegularPointCoordinates

end

end OAI
