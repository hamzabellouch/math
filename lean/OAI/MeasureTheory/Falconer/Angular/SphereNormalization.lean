import OAI.MeasureTheory.Falconer.Angular.SphereModel
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

namespace OAI

/-! # Measurable sphere normalization with a fixed value at zero -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

noncomputable def sphereNormalizeVector (w₀ : Sphere d) (v : Space d) : Space d :=
  if v = 0 then w₀ else normalize v

theorem sphereNormalizeVector_norm (w₀ : Sphere d) (v : Space d) :
    ‖sphereNormalizeVector w₀ v‖ = 1 := by
  by_cases hv : v = 0
  · simp only [sphereNormalizeVector,ite_eq_left hv,sphere_norm]
  · simp only [sphereNormalizeVector,ite_eq_right hv,norm_normalize hv]

noncomputable def normalizeToSphere (w₀ : Sphere d) (v : Space d) : Sphere d :=
  ⟨sphereNormalizeVector w₀ v,by
    rw [Metric.mem_sphere,dist_zero_right,sphereNormalizeVector_norm]⟩

theorem normalizeToSphere_measurable (w₀ : Sphere d) :
    Measurable (normalizeToSphere w₀) := by
  apply Measurable.subtype_mk
  exact Measurable.ite (by simp)
    measurable_const (measurable_id.norm.inv.smul measurable_id)

@[simp] theorem normalizeToSphere_coe_of_ne (w₀ : Sphere d) {v : Space d} (hv : v ≠ 0) :
    (normalizeToSphere w₀ v : Space d) = normalize v := by
  simp only [normalizeToSphere,sphereNormalizeVector,ite_eq_right hv]

end Falconer

end OAI
