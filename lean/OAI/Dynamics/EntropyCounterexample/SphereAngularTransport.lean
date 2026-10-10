import OAI.Dynamics.EntropyCounterexample.SphereAngularInput
import OAI.Dynamics.EntropyCounterexample.SphereCutoffTransport

namespace OAI

noncomputable section

namespace Problem340.SphereAngularInput

theorem horizontal_sphereOfComplex (z : ℂ) :
    horizontal (sphereOfComplex z).1 = (2 / (‖z‖ ^ 2 + 1) : ℝ) • z := by
  apply Complex.ext <;>
    simp [horizontal, Complex.real_smul, div_eq_mul_inv] <;> ring

theorem phase_sphereOfComplex (z : ℂ) :
    phase (sphereOfComplex z).1 = z / (‖z‖ : ℂ) := by
  have hh := phase_eq_of_positive_scale
    (x := (sphereOfComplex z).1) (z := z)
    (r := 2 / (‖z‖ ^ 2 + 1))
    (by positivity) (horizontal_sphereOfComplex z)
  rw [hh]
  simp [NormedSpace.normalize, Complex.real_smul, div_eq_mul_inv, mul_comm]

theorem angular_sphereOfComplex (k : ℕ) (z : ℂ) :
    angular k (sphereOfComplex z) =
      (SphereCutoffs.affinePreparationCutoff z : ℂ) * (z / (‖z‖ : ℂ)) ^ k := by
  change (SphereCutoffs.preparationCutoff (sphereOfComplex z) : ℂ) *
    phase (sphereOfComplex z).1 ^ k = _
  rw [SphereCutoffs.preparationCutoff_sphereOfComplex, phase_sphereOfComplex]

@[simp]
theorem angular_chartNorthPole (k : ℕ) : angular k chartNorthPole = 0 := by
  change (SphereCutoffs.preparationCutoff chartNorthPole : ℂ) * _ = 0
  simp

theorem angular_complexSphereHomeomorph (k : ℕ) (z : OnePoint ℂ) :
    angular k (complexSphereHomeomorph z) =
      (SphereCutoffs.onePointPreparationCutoff z : ℂ) *
        (OnePoint.rec 0 (fun w : ℂ => w / (‖w‖ : ℂ)) z) ^ k := by
  induction z using OnePoint.rec with
  | infty => simp
  | coe z =>
      change angular k (sphereOfComplex z) =
        (SphereCutoffs.affinePreparationCutoff z : ℂ) * (z / (‖z‖ : ℂ)) ^ k
      exact angular_sphereOfComplex k z

end Problem340.SphereAngularInput

end

end OAI
