import OAI.Dynamics.EntropyCounterexample.SphereCutoffsAffine
import OAI.Dynamics.EntropyCounterexample.SphereCharts

namespace OAI

noncomputable section

namespace Problem340.SphereCutoffs

@[simp]
theorem clockGate_sphereOfComplex (z : ℂ) :
    clockGate (sphereOfComplex z) = affineClockGate z :=
  clockGate_eq_affineClockGate (sphereOfComplex_val_two z)

@[simp]
theorem preparationCutoff_sphereOfComplex (z : ℂ) :
    preparationCutoff (sphereOfComplex z) = affinePreparationCutoff z :=
  preparationCutoff_eq_affinePreparationCutoff (sphereOfComplex_val_two z)

@[simp]
theorem clockGate_chartNorthPole : clockGate chartNorthPole = 1 := by
  apply clockGateAmbient_eq_one
  norm_num [chartNorthPole, chartNorthVector]

@[simp]
theorem preparationCutoff_chartNorthPole : preparationCutoff chartNorthPole = 0 := by
  apply preparationCutoffAmbient_eq_zero_of_high
  norm_num [chartNorthPole, chartNorthVector]

@[simp]
theorem clockGate_complexSphereHomeomorph (z : OnePoint ℂ) :
    clockGate (complexSphereHomeomorph z) = onePointClockGate z := by
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => simp

@[simp]
theorem preparationCutoff_complexSphereHomeomorph (z : OnePoint ℂ) :
    preparationCutoff (complexSphereHomeomorph z) = onePointPreparationCutoff z := by
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => simp

theorem onePointClockGate_complexSphereHomeomorph_symm (x : StandardSphere2) :
    onePointClockGate (complexSphereHomeomorph.symm x) = clockGate x := by
  rw [← clockGate_complexSphereHomeomorph, complexSphereHomeomorph.apply_symm_apply]

theorem onePointPreparationCutoff_complexSphereHomeomorph_symm (x : StandardSphere2) :
    onePointPreparationCutoff (complexSphereHomeomorph.symm x) = preparationCutoff x := by
  rw [← preparationCutoff_complexSphereHomeomorph, complexSphereHomeomorph.apply_symm_apply]

end Problem340.SphereCutoffs

end

end OAI
