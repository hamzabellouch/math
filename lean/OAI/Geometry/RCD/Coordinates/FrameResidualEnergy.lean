import OAI.Geometry.RCD.Sobolev.GammaColumnMixed
import OAI.Geometry.RCD.Sobolev.OrthonormalHarmonicLipschitz

namespace OAI

/-! # The exact energy of a residual in an orthonormal gradient frame -/

open Set Filter MeasureTheory Finset
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

def gradientFrameCoefficients {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (g : SobolevSpace μ hQ) (x : X) : Euclidean n :=
  WithLp.toLp 2 (fun i => localGamma μ hQ (u i) g x)

theorem frame_residual_energy {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (g : SobolevSpace μ hQ) (S : Set X)
    (hgram : ∀ i j, localGamma μ hQ (u i) (u j) =ᵐ[μ.restrict S]
      fun _ => if i=j then 1 else 0)
    (hframe : localGamma μ hQ g g =ᵐ[μ.restrict S]
      fun x => ∑ i, (localGamma μ hQ (u i) g x)^2) (a : Euclidean n) :
    localGamma μ hQ (g-sobolevColumnMap μ hQ u a) (g-sobolevColumnMap μ hQ u a)
      =ᵐ[μ.restrict S] fun x => ‖gradientFrameCoefficients μ hQ u g x-a‖^2 := by
  let v := sobolevColumnMap μ hQ u a
  have hcomm : ∀ᵐ x ∂μ.restrict S, ∀ i, localGamma μ hQ (u i) g x=localGamma μ hQ g (u i) x :=
    ae_all_iff.mpr fun i => ae_restrict_of_ae (localGamma_comm μ hQ (u i) g)
  filter_upwards [hframe,hcomm,
    ae_restrict_of_ae (localGamma_sub_left μ hQ g v (g-v)),
    ae_restrict_of_ae (localGamma_comm μ hQ g (g-v)),
    ae_restrict_of_ae (localGamma_sub_left μ hQ g v g),
    ae_restrict_of_ae (localGamma_comm μ hQ v (g-v)),
    ae_restrict_of_ae (localGamma_sub_left μ hQ g v v),
    ae_restrict_of_ae (localGamma_comm μ hQ v g),
    ae_restrict_of_ae (localGamma_column_right μ hQ g u a),
    localGamma_column_orthonormal μ hQ u S hgram a] with x hf hc hs h₁ h₂ h₃ h₄ h₅ hcol hv
  have hnorm : localGamma μ hQ g g x=‖gradientFrameCoefficients μ hQ u g x‖^2 := by
    rw [hf,EuclideanSpace.real_norm_sq_eq]
    rfl
  have hinner : (∑ i, a i*localGamma μ hQ g (u i) x)=
      ⟪gradientFrameCoefficients μ hQ u g x,a⟫_ℝ := by
    simp only [gradientFrameCoefficients,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
    apply sum_congr rfl
    intro i _
    rw [hc i]
  change localGamma μ hQ (g-v) (g-v) x=_
  rw [hs,h₁,h₂,h₃,h₄,h₅,hcol,hv,hnorm,hinner,norm_sub_sq_real]
  ring

end RegularPointCoordinates

end

end OAI
