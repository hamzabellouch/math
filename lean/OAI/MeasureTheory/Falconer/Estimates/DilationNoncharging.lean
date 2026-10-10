import OAI.MeasureTheory.Falconer.Geometry.ProjectionDilation

namespace OAI

/-! # Hyperplane noncharging survives positive projection normalization -/
namespace Falconer
open Set MeasureTheory
variable {d m : ℕ}

theorem dilated_hyperplane_null (μ : Measure (Space m)) {a : ℝ} (ha : 0 < a)
    (hnull : ∀ w : Space m, ‖w‖ = 1 → ∀ t : ℝ, μ {x | inner ℝ w x = t} = 0) :
    ∀ w : Space m, ‖w‖ = 1 → ∀ t : ℝ,
      μ.map (radialZoom a ha.ne' (0 : Space m)) {x | inner ℝ w x = t} = 0 := by
  intro w hw t
  rw [Measure.map_apply (radialZoom a ha.ne' (0 : Space m)).measurable
    (isClosed_eq (by fun_prop) continuous_const).measurableSet]
  have heq : radialZoom a ha.ne' (0 : Space m) ⁻¹' {x | inner ℝ w x = t} =
      {x | inner ℝ w x = t/a} := by
    ext x
    simp only [mem_preimage,mem_ofPred_eq,radialZoom_apply,sub_zero,inner_smul_right]
    rw [eq_div_iff ha.ne']
    constructor <;> intro h <;> nlinarith only [h]
  rw [heq]
  exact hnull w hw (t/a)

theorem dilated_projection_hyperplane_null (μ : Measure (Space d))
    (P : Space d →L[ℝ] Space m) {a : ℝ} (ha : 0 < a)
    (hnull : ∀ w : Space m, ‖w‖ = 1 → ∀ t : ℝ,
      μ.map P {x | inner ℝ w x = t} = 0) :
    ∀ w : Space m, ‖w‖ = 1 → ∀ t : ℝ,
      μ.map (a • P) {x | inner ℝ w x = t} = 0 := by
  rw [map_smul_linear μ P ha]
  exact dilated_hyperplane_null (μ.map P) ha hnull

end Falconer

end OAI
