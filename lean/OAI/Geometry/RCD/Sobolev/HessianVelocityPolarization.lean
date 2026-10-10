import OAI.Geometry.RCD.Sobolev.HessianActionChain

namespace OAI

/-! # Velocity and logarithmic-density polarization of the Hessian action -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem localGamma_sub_right (f g h : SobolevSpace μ Q) :
    localGamma μ Q f (g-h) =ᵐ[μ]
      fun x => localGamma μ Q f g x-localGamma μ Q f h x := by
  filter_upwards [localGamma_comm μ Q f (g-h),localGamma_sub_left μ Q g h f,
    localGamma_comm μ Q g f,localGamma_comm μ Q h f] with x h₁ h₂ h₃ h₄
  rw [h₁,h₂,h₃,h₄]

theorem localHessianAction_velocity_polarization
    (f u v fu fv uu vv uv : SobolevSpace μ Q) :
    (fun x => localHessianAction μ Q f (v-u) (v-u) (fv-fu) (fv-fu)
        (uu+vv-(2:ℝ) • uv) x -
      localHessianAction μ Q f (v+u) (v+u) (fv+fu) (fv+fu)
        (uu+vv+(2:ℝ) • uv) x) =ᵐ[μ]
      fun x => -4*localHessianAction μ Q f u v fu fv uv x := by
  filter_upwards [localGamma_sub_left μ Q v u (fv-fu),
    localGamma_sub_right μ Q v fv fu,localGamma_sub_right μ Q u fv fu,
    localGamma_add_left μ Q v u (fv+fu),
    localGamma_add_right μ Q v fv fu,localGamma_add_right μ Q u fv fu,
    localGamma_sub_right μ Q f (uu+vv) ((2:ℝ) • uv),
    localGamma_add_right μ Q f (uu+vv) ((2:ℝ) • uv),
    localGamma_smul_right μ Q 2 f uv] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
  dsimp only [localHessianAction]
  rw [h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉]
  ring

theorem localGamma_velocity_square_reps {Ω : Set X}
    (u v uu vv uv : SobolevSpace μ Q)
    (huu : SobolevSpace.toLp μ Q uu =ᵐ[μ.restrict Ω] localGamma μ Q u u)
    (hvv : SobolevSpace.toLp μ Q vv =ᵐ[μ.restrict Ω] localGamma μ Q v v)
    (huv : SobolevSpace.toLp μ Q uv =ᵐ[μ.restrict Ω] localGamma μ Q u v) :
    (SobolevSpace.toLp μ Q (uu+vv-(2:ℝ) • uv) =ᵐ[μ.restrict Ω]
      localGamma μ Q (v-u) (v-u)) ∧
    (SobolevSpace.toLp μ Q (uu+vv+(2:ℝ) • uv) =ᵐ[μ.restrict Ω]
      localGamma μ Q (v+u) (v+u)) := by
  have hsum := Lp.coeFn_add (SobolevSpace.toLp μ Q uu) (SobolevSpace.toLp μ Q vv)
  have hscale := Lp.coeFn_smul (2:ℝ) (SobolevSpace.toLp μ Q uv)
  have hminus := Lp.coeFn_sub (SobolevSpace.toLp μ Q (uu+vv))
    (SobolevSpace.toLp μ Q ((2:ℝ) • uv))
  have hplus := Lp.coeFn_add (SobolevSpace.toLp μ Q (uu+vv))
    (SobolevSpace.toLp μ Q ((2:ℝ) • uv))
  have both : ∀ᵐ x ∂μ.restrict Ω,
      SobolevSpace.toLp μ Q (uu+vv-(2:ℝ) • uv) x = localGamma μ Q (v-u) (v-u) x ∧
      SobolevSpace.toLp μ Q (uu+vv+(2:ℝ) • uv) x = localGamma μ Q (v+u) (v+u) x := by
    filter_upwards [huu,hvv,huv,ae_restrict_of_ae hsum,ae_restrict_of_ae hscale,
      ae_restrict_of_ae hminus,ae_restrict_of_ae hplus,
      ae_restrict_of_ae (localGamma_sub_left μ Q v u (v-u)),
      ae_restrict_of_ae (localGamma_sub_right μ Q v v u),
      ae_restrict_of_ae (localGamma_sub_right μ Q u v u),
      ae_restrict_of_ae (localGamma_add_left μ Q v u (v+u)),
      ae_restrict_of_ae (localGamma_add_right μ Q v v u),
      ae_restrict_of_ae (localGamma_add_right μ Q u v u),
      ae_restrict_of_ae (localGamma_comm μ Q v u)]
      with x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄
    simp only [map_add,map_sub,map_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at h₄ h₅ h₆ h₇ ⊢
    rw [h₆,h₇,h₄,h₅,h₁,h₂,h₃,h₈,h₉,h₁₀,h₁₁,h₁₂,h₁₃,h₁₄]
    constructor <;> ring
  exact ⟨both.mono fun _ h => h.1,both.mono fun _ h => h.2⟩

end RegularPointCoordinates

end

end OAI
