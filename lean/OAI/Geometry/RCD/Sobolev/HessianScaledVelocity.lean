import OAI.Geometry.RCD.Sobolev.HessianVelocityPolarization

namespace OAI

/-! # Physical scaling of the velocity and osmotic Hessian directions -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem localHessianAction_scaled_diagonal (f u fu uu : SobolevSpace μ Q) (c : ℝ) :
    localHessianAction μ Q f (c • u) (c • u) (c • fu) (c • fu) ((c^2) • uu)
      =ᵐ[μ] fun x => c^2*localHessianAction μ Q f u u fu fu uu x := by
  filter_upwards [localGamma_smul_left μ Q c u (c • fu),
    localGamma_smul_right μ Q c u fu,localGamma_smul_right μ Q (c^2) f uu]
    with x h₁ h₂ h₃
  dsimp only [localHessianAction]
  rw [h₁,h₂,h₃]
  ring

theorem localHessianAction_scaled_velocity
    (f u v fu fv uu vv uv : SobolevSpace μ Q) (c : ℝ) :
    (fun x => localHessianAction μ Q f (c • (v-u)) (c • (v-u))
        (c • (fv-fu)) (c • (fv-fu)) ((c^2) • (uu+vv-(2:ℝ) • uv)) x -
      localHessianAction μ Q f (c • (v+u)) (c • (v+u))
        (c • (fv+fu)) (c • (fv+fu)) ((c^2) • (uu+vv+(2:ℝ) • uv)) x) =ᵐ[μ]
      fun x => -4*c^2*localHessianAction μ Q f u v fu fv uv x := by
  filter_upwards [localHessianAction_scaled_diagonal μ Q f (v-u) (fv-fu)
      (uu+vv-(2:ℝ) • uv) c,
    localHessianAction_scaled_diagonal μ Q f (v+u) (fv+fu) (uu+vv+(2:ℝ) • uv) c,
    localHessianAction_velocity_polarization μ Q f u v fu fv uu vv uv]
    with x h₁ h₂ h₃
  rw [h₁,h₂,← mul_sub,h₃]
  ring

theorem localGamma_scaled_square_rep {Ω : Set X}
    (u G : SobolevSpace μ Q) (c : ℝ)
    (hG : SobolevSpace.toLp μ Q G =ᵐ[μ.restrict Ω] localGamma μ Q u u) :
    SobolevSpace.toLp μ Q ((c^2) • G) =ᵐ[μ.restrict Ω]
      localGamma μ Q (c • u) (c • u) := by
  filter_upwards [hG,ae_restrict_of_ae (Lp.coeFn_smul (c^2) (SobolevSpace.toLp μ Q G)),
    ae_restrict_of_ae (localGamma_smul_left μ Q c u (c • u)),
    ae_restrict_of_ae (localGamma_smul_right μ Q c u u)] with x h₁ h₂ h₃ h₄
  simp only [map_smul,Pi.smul_apply,smul_eq_mul] at h₂ ⊢
  rw [h₂,h₁,h₃,h₄]
  ring

end RegularPointCoordinates

end

end OAI
