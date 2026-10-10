import OAI.MeasureTheory.Falconer.Angular.SphereCapBox
import OAI.MeasureTheory.Falconer.Estimates.RotatedLaws
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

namespace OAI

/-! # The actual spherical surface measure has its dimensional cap bound -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal

theorem sphere_cap_bound (n : ℕ) (w : Sphere (n+1)) {r : ℝ} (hr : 0 ≤ r) :
    sphereMeasure (n+1) (ball w r) ≤
      ENNReal.ofReal ((((n+1:ℕ):ℝ)*(2:ℝ)^(n+1))*r^n) := by
  let north := gnomonicChart (0 : Space n)
  let e := (ℝ ∙ ((north:Space (n+1))-(w:Space (n+1))))ᗮ.reflection
  have he : e (north:Space (n+1)) = (w:Space (n+1)) :=
    Submodule.reflection_sub ((sphere_norm north).trans (sphere_norm w).symm)
  have he' : sphereMap e north = w := Subtype.ext he
  have hrw := rotated_direction_ball (sphereMeasure (n+1)) e w r
  rw [(sphereMap_measurePreserving e).map_eq] at hrw
  have hn : sphereMap e.symm w = north := by rw [← he',sphereMap_apply_symm]
  rw [hn] at hrw
  rw [hrw]
  apply (north_sphere_cap_bound n hr).trans_eq
  congr 1
  rw [mul_pow,pow_succ]
  ring

noncomputable def surfaceMeasure (d : ℕ) : Measure (Space d) :=
  (sphereMeasure d).map (Subtype.val : Sphere d → Space d)

instance surfaceMeasure_finite (d : ℕ) : IsFiniteMeasure (surfaceMeasure d) := by
  unfold surfaceMeasure
  infer_instance

theorem surfaceMeasure_ball_bound (n : ℕ) (w : Space (n+1)) (hw : ‖w‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) :
    surfaceMeasure (n+1) (ball w r) ≤
      ENNReal.ofReal ((((n+1:ℕ):ℝ)*(2:ℝ)^(n+1))*r^n) := by
  let w' : Sphere (n+1) := ⟨w,by simpa only [mem_sphere,dist_zero_right] using hw⟩
  rw [surfaceMeasure,Measure.map_apply measurable_subtype_coe measurableSet_ball]
  exact sphere_cap_bound n w' hr

end Falconer

end OAI
