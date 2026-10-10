import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationalTwistLift

namespace OAI

/-! # Conjugation in the inverse-character graph -/

noncomputable section
namespace PolycyclicRecognition

variable {N D G K : Type*} [Group N] [Group D] [Group G] [CommGroup K]
  [TopologicalSpace G] [TopologicalSpace K]
  (α : K →* MulAut G) (τ : G →* K) (hinv : ∀ k g, τ (α k g) = τ g)
  (iN : N →* G) (iD : D →* G)
  (hN : ∀ n m, α ((τ (iN n))⁻¹) (iN m) = iN m)
  (hD : ∀ d e, α ((τ (iD d))⁻¹) (iD e) = iD e)

omit [TopologicalSpace G] [TopologicalSpace K] in
/-- The graph conjugation is the original conjugation followed by the
inverse compact rotation. -/
theorem rotationalTwistLift_conjugation_left (d : D) (n : N)
    (hn : τ (iN n) = 1) :
    ((rotationalTwistLift α τ hinv iD hD d *
      rotationalTwistLift α τ hinv iN hN n *
      (rotationalTwistLift α τ hinv iD hD d)⁻¹).val.left) =
      α ((τ (iD d))⁻¹) (iD d * iN n * (iD d)⁻¹) := by
  change (iD d * α ((τ (iD d))⁻¹) (iN n)) *
    α ((τ (iD d))⁻¹ * (τ (iN n))⁻¹)
      (α (((τ (iD d))⁻¹)⁻¹) ((iD d)⁻¹)) = _
  rw [hn, inv_one, mul_one, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  change (iD d * α ((τ (iD d))⁻¹) (iN n)) * (iD d)⁻¹ = _
  rw [(α ((τ (iD d))⁻¹)).map_mul, (α ((τ (iD d))⁻¹)).map_mul,
    (α ((τ (iD d))⁻¹)).map_inv, hD d d]

end PolycyclicRecognition

end

end OAI
