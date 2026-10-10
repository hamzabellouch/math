import OAI.Geometry.RCD.Coordinates.FrameVelocityError

namespace OAI

/-! # The same spatial error controls the coefficient norm and scalar velocity -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
theorem frame_coefficients_error_identity {n : ℕ} (u : Fin n → SobolevSpace μ Q)
    (g : SobolevSpace μ Q) (x : X) :
    ‖gradientFrameCoefficients μ Q u g x‖^2=
      localGamma μ Q g g x-frameEnergyError μ Q u g x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, (localGamma μ Q (u i) g x)^2)=_
  unfold frameEnergyError
  ring

omit [ProperSpace X] in
theorem frame_coefficients_velocity_error_le {n : ℕ} (u : Fin n → SobolevSpace μ Q)
    (g : SobolevSpace μ Q) (x : X) :
    ‖gradientFrameCoefficients μ Q u g x‖^2≤localGamma μ Q g g x+frameVelocityError μ Q u g x := by
  have he := frame_coefficients_error_identity μ Q u g x
  have hE := neg_le_abs (frameEnergyError μ Q u g x)
  have hnn := mul_nonneg (gramDefect_nonneg μ Q u x) (sq_nonneg ‖gradientFrameCoefficients μ Q u g x‖)
  unfold frameVelocityError
  linarith only [he,hE,hnn]

omit [ProperSpace X] in
theorem frame_coefficients_velocity_bound {n : ℕ} (u : Fin n → SobolevSpace μ Q)
    (g : SobolevSpace μ Q) {S : Set X} {L : ℝ}
    (hg : ∀ᵐ x ∂μ.restrict S, localGamma μ Q g g x≤L^2) :
    ∀ᵐ x ∂μ.restrict S,
      ‖gradientFrameCoefficients μ Q u g x‖^2≤L^2+frameVelocityError μ Q u g x := by
  filter_upwards [hg] with x hx
  exact (frame_coefficients_velocity_error_le μ Q u g x).trans (add_le_add hx le_rfl)

end RegularPointCoordinates

end

end OAI
