import OAI.Geometry.RCD.Coordinates.FrameEnergyError
import OAI.Geometry.RCD.Harmonic.GramQuadraticDefect

namespace OAI

/-! # Exact residual energy and its quantitative Gram-error bound -/

open Set Filter MeasureTheory Finset
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem frame_residual_energy_expansion {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (g : SobolevSpace μ hQ) (a : Euclidean n) :
    ∀ᵐ x ∂μ, localGamma μ hQ (g-sobolevColumnMap μ hQ u a) (g-sobolevColumnMap μ hQ u a) x=
      ‖gradientFrameCoefficients μ hQ u g x-a‖^2+frameEnergyError μ hQ u g x+
        (localGamma μ hQ (sobolevColumnMap μ hQ u a) (sobolevColumnMap μ hQ u a) x-‖a‖^2) := by
  let v := sobolevColumnMap μ hQ u a
  have hcomm : ∀ᵐ x ∂μ, ∀ i, localGamma μ hQ (u i) g x=localGamma μ hQ g (u i) x :=
    ae_all_iff.mpr fun i => localGamma_comm μ hQ (u i) g
  filter_upwards [hcomm,localGamma_sub_left μ hQ g v (g-v),
    localGamma_comm μ hQ g (g-v),localGamma_sub_left μ hQ g v g,
    localGamma_comm μ hQ v (g-v),localGamma_sub_left μ hQ g v v,
    localGamma_comm μ hQ v g,localGamma_column_right μ hQ g u a]
    with x hc hs h₁ h₂ h₃ h₄ h₅ hcol
  have hE : localGamma μ hQ g g x=frameEnergyError μ hQ u g x+
      ‖gradientFrameCoefficients μ hQ u g x‖^2 := by
    rw [frameEnergyError,EuclideanSpace.real_norm_sq_eq]
    dsimp only [gradientFrameCoefficients]
    ring
  have hinner : (∑ i, a i*localGamma μ hQ g (u i) x)=
      ⟪gradientFrameCoefficients μ hQ u g x,a⟫_ℝ := by
    simp only [gradientFrameCoefficients,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
    exact sum_congr rfl (fun i _ => by rw [hc i])
  change localGamma μ hQ (g-v) (g-v) x=_
  rw [hs,h₁,h₂,h₃,h₄,h₅,hcol,hE,hinner,norm_sub_sq_real]
  ring

theorem frame_residual_energy_le {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (g : SobolevSpace μ hQ) (a : Euclidean n) :
    ∀ᵐ x ∂μ, localGamma μ hQ (g-sobolevColumnMap μ hQ u a) (g-sobolevColumnMap μ hQ u a) x≤
      ‖gradientFrameCoefficients μ hQ u g x-a‖^2+|frameEnergyError μ hQ u g x|+
        gramDefect μ hQ u x*‖a‖^2 := by
  filter_upwards [frame_residual_energy_expansion μ hQ u g a,
    localGamma_column_defect μ hQ u a] with x hx hcol
  rw [hx]
  have hh := (abs_le.mp hcol).2
  linarith [le_abs_self (frameEnergyError μ hQ u g x)]

end RegularPointCoordinates

end

end OAI
