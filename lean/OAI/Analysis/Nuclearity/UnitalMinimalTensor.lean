import OAI.Analysis.WeakInfiniteness.TensorAbsorption

namespace OAI

/-! The unit and the two unital legs of a minimal tensor product. The unital
structure is exposed as a definition for local use in the factor argument. -/

noncomputable section

namespace WeakPureInfiniteness

variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]

theorem minimalTensor_unit_left (x : MinimalTensor A B) :
    minimalElementary (1 : A) (1 : B) * x = x := by
  let S : Submodule ℂ (MinimalTensor A B) :=
    { carrier := {x | minimalElementary (1 : A) (1 : B) * x = x}
      zero_mem' := mul_zero _
      add_mem' := fun hx hy => by dsimp at hx hy ⊢; rw [mul_add, hx, hy]
      smul_mem' := fun c x hx => by dsimp at hx ⊢; rw [mul_smul_comm, hx] }
  have hs : S = ⊤ := by
    apply minimal_elementary_span_dense S
      (isClosed_eq (continuous_const.mul continuous_id) continuous_id)
    intro a b
    change minimalElementary (1 : A) (1 : B) * minimalElementary a b = _
    rw [← minimalElementary_mul, one_mul, one_mul]
  have hx : x ∈ S := by rw [hs]; trivial
  exact hx

theorem minimalTensor_unit_right (x : MinimalTensor A B) :
    x * minimalElementary (1 : A) (1 : B) = x := by
  let S : Submodule ℂ (MinimalTensor A B) :=
    { carrier := {x | x * minimalElementary (1 : A) (1 : B) = x}
      zero_mem' := zero_mul _
      add_mem' := fun hx hy => by dsimp at hx hy ⊢; rw [add_mul, hx, hy]
      smul_mem' := fun c x hx => by dsimp at hx ⊢; rw [smul_mul_assoc, hx] }
  have hs : S = ⊤ := by
    apply minimal_elementary_span_dense S
      (isClosed_eq (continuous_id.mul continuous_const) continuous_id)
    intro a b
    change minimalElementary a b * minimalElementary (1 : A) (1 : B) = _
    rw [← minimalElementary_mul, mul_one, mul_one]
  have hx : x ∈ S := by rw [hs]; trivial
  exact hx

abbrev minimalTensorUnitalStructure : CStarAlgebra (MinimalTensor A B) := by
  let _ : IsUnital (MinimalTensor A B) :=
    ⟨⟨minimalElementary (1 : A) (1 : B), fun x =>
      ⟨minimalTensor_unit_left A B x, minimalTensor_unit_right A B x⟩⟩⟩
  exact IsUnital.toCStarAlgebra

namespace UnitalMinimalTensor

local instance : CStarAlgebra (MinimalTensor A B) := minimalTensorUnitalStructure A B

theorem one_eq : (1 : MinimalTensor A B) = minimalElementary (1 : A) (1 : B) := by
  have h := minimalTensor_unit_left A B (1 : MinimalTensor A B)
  rw [mul_one] at h
  exact h.symm

def leftEmbedding : A →⋆ₐ[ℂ] MinimalTensor A B :=
  { minimalLeftEmbedding A B with
    map_one' := (one_eq A B).symm
    commutes' := fun c => by
      rw [Algebra.algebraMap_eq_smul_one]
      change minimalElementary (c • (1 : A)) (1 : B) = _
      rw [minimalElementary_smul_left]
      change c • minimalElementary (1 : A) (1 : B) = algebraMap ℂ (MinimalTensor A B) c
      rw [Algebra.algebraMap_eq_smul_one, one_eq] }

def rightEmbedding : B →⋆ₐ[ℂ] MinimalTensor A B where
  toFun b := minimalElementary 1 b
  map_zero' := map_zero (minimalElementaryRightLinear (1 : A))
  map_add' b c := map_add (minimalElementaryRightLinear (1 : A)) b c
  map_mul' b c := by rw [← minimalElementary_mul, one_mul]
  map_one' := (one_eq A B).symm
  map_star' b := by rw [← minimalElementary_star, star_one]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    change minimalElementary (1 : A) (c • (1 : B)) = _
    rw [show minimalElementary (1 : A) (c • (1 : B)) =
      c • minimalElementary (1 : A) (1 : B) from map_smul (minimalElementaryRightLinear (1 : A)) c 1]
    rw [Algebra.algebraMap_eq_smul_one, one_eq]

theorem legs_mul (a : A) (b : B) :
    leftEmbedding A B a * rightEmbedding A B b = minimalElementary a b := by
  change minimalElementary a 1 * minimalElementary 1 b = _
  rw [← minimalElementary_mul, mul_one, one_mul]

theorem legs_commute (a : A) (b : B) : Commute (leftEmbedding A B a) (rightEmbedding A B b) := by
  change minimalElementary a 1 * minimalElementary 1 b =
    minimalElementary 1 b * minimalElementary a 1
  rw [← minimalElementary_mul, ← minimalElementary_mul, one_mul, mul_one, one_mul, mul_one]

end UnitalMinimalTensor
end WeakPureInfiniteness

end

end OAI
