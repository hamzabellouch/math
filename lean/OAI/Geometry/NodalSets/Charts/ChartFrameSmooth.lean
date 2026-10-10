import OAI.Geometry.NodalSets.Charts.CircleChartFactor
import OAI.Geometry.NodalSets.Charts.SmoothInverseChart

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff Topology
noncomputable section
attribute [local instance] finrank_real_complex_fact'
local instance : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

lemma sphereChartDerivative_eq_fderiv (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) :
    sphereChartDerivative p y =
      fderiv ℝ ((Subtype.val : Base → AmbientBase) ∘ (extChartAt (𝓡 4) p).symm) y := by
  exact (inverse_chart_comp_derivative _ (contMDiff_coe_sphere (n := 4)) p hy).symm

lemma sphereChartDerivative_smooth_at (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) :
    ContDiffAt ℝ ∞ (sphereChartDerivative p) y := by
  apply (smooth_inverse_chart_derivative _ (contMDiff_coe_sphere (n := 4)) p hy).congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with z hz
  exact sphereChartDerivative_eq_fderiv p hz

lemma sphereChartFrame_smooth_at (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) (i : Fin 5) (j : Fin 4) :
    ContDiffAt ℝ ∞ (fun z ↦ sphereChartFrame p z i j) y := by
  simp_rw [sphereChartFrame_apply]
  exact (contDiffAt_piLp_apply 2).comp y
    ((sphereChartDerivative_smooth_at p hy).clm_apply contDiffAt_const)

lemma circleChartDerivative_eq_fderiv (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) :
    circleChartDerivative p y =
      fderiv ℝ ((fun z : Circle ↦ (z : ℂ)) ∘ (extChartAt (𝓡 1) p).symm) y := by
  exact (inverse_chart_comp_derivative _ (contMDiff_coe_sphere (E := ℂ) (n := 1)) p hy).symm

lemma circleChartDerivative_smooth_at (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) :
    ContDiffAt ℝ ∞ (circleChartDerivative p) y := by
  apply (smooth_inverse_chart_derivative _ (contMDiff_coe_sphere (E := ℂ) (n := 1)) p hy).congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with z hz
  exact circleChartDerivative_eq_fderiv p hz

lemma circleChartFactor_smooth_at (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) :
    ContDiffAt ℝ ∞ (circleChartFactor p) y := by
  have h := (circleChartDerivative_smooth_at p hy).clm_apply
    (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 1) ℝ 0))
  convert! h.inner ℝ h using 1
  simp only [real_inner_self_eq_norm_sq]
  rfl

lemma circleChartDensity_smooth_at (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) :
    ContDiffAt ℝ ∞ (fun z ↦ Real.sqrt (circleChartFactor p z)) y :=
  (circleChartFactor_smooth_at p hy).sqrt (circleChartFactor_pos p hy).ne'

end
end Yau.Target

end OAI
