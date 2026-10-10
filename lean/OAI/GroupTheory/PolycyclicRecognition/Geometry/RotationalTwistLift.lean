import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactRotationalTwist

namespace OAI

/-! # Subgroups whose multiplication is preserved by a rotational twist -/

noncomputable section
namespace PolycyclicRecognition

variable {A G K : Type*} [Group A] [Group G] [CommGroup K]
  [TopologicalSpace G] [TopologicalSpace K]
  (α : K →* MulAut G) (τ : G →* K)
  (hinv : ∀ k g, τ (α k g) = τ g)
  (f : A →* G) (hfix : ∀ a b, α ((τ (f a))⁻¹) (f b) = f b)

/-- The inverse-character graph is multiplicative on this subgroup. -/
def rotationalTwistLift : A →* rotationalTwist α τ hinv where
  toFun a := ⟨⟨f a, (τ (f a))⁻¹⟩, rfl⟩
  map_one' := by
    apply Subtype.ext
    apply SemidirectProduct.ext <;> simp
  map_mul' a b := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · change f (a * b) = f a * α ((τ (f a))⁻¹) (f b)
      rw [hfix, map_mul]
    · change (τ (f (a * b)))⁻¹ = (τ (f a))⁻¹ * (τ (f b))⁻¹
      rw [map_mul, map_mul, mul_inv_rev, mul_comm]

omit [TopologicalSpace G] [TopologicalSpace K] in
@[simp] theorem rotationalTwistLift_left (a : A) :
    (rotationalTwistLift α τ hinv f hfix a).val.left = f a := rfl

variable [TopologicalSpace A] [IsTopologicalGroup K]
attribute [local instance] semidirectProductTopology

/-- The lift retains exactly the original topology on its image. -/
theorem continuous_rotationalTwistLift (hτ : Continuous τ) (hf : Continuous f) :
    Continuous (rotationalTwistLift α τ hinv f hfix) := by
  exact (rotationalTwistHomeomorph α τ hinv hτ).symm.continuous.comp hf

end PolycyclicRecognition

end

end OAI
