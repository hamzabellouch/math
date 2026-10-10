import OAI.Dynamics.EntropyCounterexample.SphereChartLimits
import OAI.Dynamics.EntropyCounterexample.SpherePerturbation

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.SphereMainUpdate

@[simp] theorem update_sphereOfComplex (c z : ℂ) :
    update c (sphereOfComplex z) = sphereOfComplex (z ^ 2 + c) := by
  have hz : sphereOfComplex z ≠ SphereDoubling.north := by
    rw [← SphereChartLimits.north_eq]
    exact sphereOfComplex_ne_north z
  have hout : update c (sphereOfComplex z) ≠ chartNorthPole := by
    rw [SphereChartLimits.north_eq]
    exact update_ne_north c _ hz
  calc
    update c (sphereOfComplex z) =
        sphereOfComplex (sphereToComplex (update c (sphereOfComplex z))) :=
      (sphereOfComplex_sphereToComplex hout).symm
    _ = sphereOfComplex (SphereTranslation.chart (update c (sphereOfComplex z)).1) := by
      rw [SphereChartLimits.sphereToComplex_eq_chart hout]
    _ = sphereOfComplex (z ^ 2 + c) := by
      rw [chart_update c _ hz, SphereChartLimits.chart_sphereOfComplex]

theorem update_complexSphereHomeomorph (c : ℂ) (z : OnePoint ℂ) :
    update c (complexSphereHomeomorph z) =
      complexSphereHomeomorph (perturbedSquare c z) := by
  induction z using OnePoint.rec with
  | infty => simp [SphereChartLimits.north_eq]
  | coe z => simp

theorem update_eq_transport (c : ℂ) :
    update c =
      complexSphereHomeomorph ∘ perturbedSquare c ∘ complexSphereHomeomorph.symm := by
  funext x
  simpa only [Homeomorph.apply_symm_apply, Function.comp_apply] using
    update_complexSphereHomeomorph c (complexSphereHomeomorph.symm x)

theorem coe_complexSphereHomeomorph_perturbedSquare (c : ℂ) (z : OnePoint ℂ) :
    (complexSphereHomeomorph (perturbedSquare c z)).1 =
      ambient c (complexSphereHomeomorph z).1 := by
  rw [← update_complexSphereHomeomorph]
  rfl

end Problem340.SphereMainUpdate

end

end OAI
