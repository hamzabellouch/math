import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationalTwistLift

namespace OAI

/-! # Characters preserved by a rotational twist -/

noncomputable section
namespace PolycyclicRecognition

variable {G K A : Type*} [Group G] [CommGroup K] [Monoid A]
  (α : K →* MulAut G) (τ : G →* K) (hinv : ∀ k g, τ (α k g) = τ g)
  (π : G →* A) (hπ : ∀ k g, π (α k g) = π g)

/-- An invariant character is still a homomorphism on the modified group. -/
def rotationalTwistCharacter : rotationalTwist α τ hinv →* A where
  toFun p := π p.val.left
  map_one' := π.map_one
  map_mul' p q := by
    change π (p.val.left * α p.val.right q.val.left) = π p.val.left * π q.val.left
    rw [map_mul, hπ]

@[simp] theorem rotationalTwistCharacter_apply (p : rotationalTwist α τ hinv) :
    rotationalTwistCharacter α τ hinv π hπ p = π p.val.left := rfl

variable [TopologicalSpace G] [TopologicalSpace K] [TopologicalSpace A]
attribute [local instance] semidirectProductTopology

/-- Continuity is retained in the original topology. -/
theorem continuous_rotationalTwistCharacter (h : Continuous π) :
    Continuous (rotationalTwistCharacter α τ hinv π hπ) :=
  h.comp ((continuous_semidirect_left α).comp continuous_subtype_val)

end PolycyclicRecognition

end

end OAI
