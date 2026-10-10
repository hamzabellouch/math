import OAI.GroupTheory.PolycyclicRecognition.Algebra.InvariantSubspaceDeterminant
import Mathlib.LinearAlgebra.Quotient.Basic

namespace OAI

/-! # The action induced on an invariant quotient -/

noncomputable section
namespace PolycyclicRecognition

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

def quotientLinearAction (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W) : G →* ((V ⧸ W) ≃ₗ[K] (V ⧸ W)) where
  toFun g :=
    { W.mapQ W (ρ g).toLinearMap (hW g) with
      invFun := W.mapQ W (ρ g⁻¹).toLinearMap (hW g⁻¹)
      left_inv := by
        intro v
        obtain ⟨v, rfl⟩ := W.mkQ_surjective v
        change W.mkQ (ρ g⁻¹ (ρ g v)) = W.mkQ v
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := by
        intro v
        obtain ⟨v, rfl⟩ := W.mkQ_surjective v
        change W.mkQ (ρ g (ρ g⁻¹ v)) = W.mkQ v
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl }
  map_one' := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨v, rfl⟩ := W.mkQ_surjective v
    change W.mkQ (ρ 1 v) = W.mkQ v
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨v, rfl⟩ := W.mkQ_surjective v
    change W.mkQ (ρ (g * h) v) = W.mkQ (ρ g (ρ h v))
    rw [map_mul]
    rfl

@[simp] theorem quotientLinearAction_mkQ (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W) (g : G) (v : V) :
    quotientLinearAction ρ W hW g (W.mkQ v) = W.mkQ (ρ g v) := rfl

end PolycyclicRecognition

end

end OAI
