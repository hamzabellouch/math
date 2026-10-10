import OAI.Analysis.IrrationalRotation.Rotation.ContinuousWeightOperatorBridge
import OAI.Analysis.IrrationalRotation.Rotation.RotationProjectionTransport

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem continuousWeight_hasOnlyTrivialInvariantProjections
    (d : BackgroundBumpData θ)
    (hstar : HasOnlyTrivialInvariantProjections (Rotation.algebra θ)
      (Rotation.U * Rotation.measurableRepresentation θ
        (fun x => (p.measurableWeight θ x : ℂ)) 1 zero_le_one
        hp.measurable_complexParameterWeight hp.norm_complexParameterWeight_le_one)) :
    HasOnlyTrivialInvariantProjections (Rotation.algebra θ)
      (Rotation.weightedReal θ
        ⟨p.continuousWeight θ d, (hp.isContinuousCircleWeight_continuousWeight d).1⟩) := by
  let f : C(Circle, ℝ) :=
    ⟨p.continuousWeight θ d, (hp.isContinuousCircleWeight_continuousWeight d).1⟩
  let H := Rotation.exponentialTransfer θ (p.continuousTransfer θ d)
  let Tstar := Rotation.U * Rotation.measurableRepresentation θ
    (fun x => (p.measurableWeight θ x : ℂ)) 1 zero_le_one
    hp.measurable_complexParameterWeight hp.norm_complexParameterWeight_le_one
  have h := hp.continuousWeight_natural_intertwining d
  let hD : ∀ ξ : H.domain, Rotation.weightedReal θ f ξ.val ∈ H.domain :=
    fun ξ => (h ξ).choose
  have hI : ∀ ξ : H.domain, H ⟨Rotation.weightedReal θ f ξ.val, hD ξ⟩ =
      (Real.exp (-1) : ℂ) • Tstar (H ξ) := fun ξ => (h ξ).choose_spec
  exact Rotation.hasOnlyTrivialInvariantProjections_of_scaled_exponentialTransfer θ
    (measurable_continuousTransfer d) (Rotation.weightedReal θ f) Tstar
    (Real.exp (-1) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hD hI hstar

end Invariant233.CircleParameterLaws

end

end OAI
