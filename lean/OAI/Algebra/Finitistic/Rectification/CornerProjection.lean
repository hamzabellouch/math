import OAI.Algebra.Finitistic.Rectification.CornerSpaces
import OAI.Algebra.Finitistic.Rectification.InducedColumns

namespace OAI
noncomputable section

namespace LittleFinitistic.CornerProjection
open ThreeVertexAlgebra CornerSpaces
universe u
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)

private theorem videm (i : Fin 3) : vertex μ i * vertex μ i = vertex μ i :=
  (directedSystem μ).idem i

theorem corner_left_fixed (i j : Fin 3) (x : corner μ i j) : vertex μ i * x.val = x.val := by
  have hx := x.property
  change vertex μ i * x.val * vertex μ j = x.val at hx
  calc
    vertex μ i * x.val = vertex μ i * (vertex μ i * x.val * vertex μ j) := congrArg (fun a : ThreeVertexAlgebra μ => vertex μ i * a) hx.symm
    _ = vertex μ i * x.val * vertex μ j := by simp only [← mul_assoc,videm]
    _ = x.val := hx

theorem corner_right_fixed (i j : Fin 3) (x : corner μ i j) : x.val * vertex μ j = x.val := by
  have hx := x.property
  change vertex μ i * x.val * vertex μ j = x.val at hx
  calc
    x.val * vertex μ j = (vertex μ i * x.val * vertex μ j) * vertex μ j := congrArg (fun a : ThreeVertexAlgebra μ => a * vertex μ j) hx.symm
    _ = vertex μ i * x.val * vertex μ j := by rw [mul_assoc,videm]
    _ = x.val := hx

theorem ideal_right_fixed (j : Fin 3)
    (x : ExternalTensor.leftIdeal (ThreeVertexAlgebra μ) (vertex μ j)) :
    x.val * vertex μ j = x.val := by
  obtain ⟨b,hb⟩ := x.property
  change b * vertex μ j = x.val at hb
  rw [← hb,mul_assoc,videm]

/-- Left multiplication by e_i on the actual induced-column first factor B e_j. -/
def projection (i j : Fin 3) :
    ExternalTensor.leftIdeal (ThreeVertexAlgebra μ) (vertex μ j) →ₗ[k]
    ExternalTensor.leftIdeal (ThreeVertexAlgebra μ) (vertex μ j) where
  toFun x := ⟨vertex μ i * x.val,⟨vertex μ i * x.val,by
    change (vertex μ i * x.val) * vertex μ j = vertex μ i * x.val
    rw [mul_assoc,ideal_right_fixed]⟩⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' c x := Subtype.ext (mul_smul_comm _ _ _)

@[simp] theorem projection_apply (i j : Fin 3) (x) :
    ((projection μ i j) x).val = vertex μ i * x.val := rfl

theorem projection_idempotent (i j : Fin 3) :
    (projection μ i j).comp (projection μ i j) = projection μ i j := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change vertex μ i * (vertex μ i * x.val) = vertex μ i * x.val
  rw [← mul_assoc,videm]

/-- The image of the actual column projector is the concrete two-sided path corner. -/
def rangeEquiv (i j : Fin 3) : (projection μ i j).range ≃ₗ[k] corner μ i j where
  toFun x := ⟨x.val.val,by
    obtain ⟨y,hy⟩ := x.property
    have h := congrArg Subtype.val hy
    change vertex μ i * y.val = x.val.val at h
    change vertex μ i * x.val.val * vertex μ j = x.val.val
    rw [← h,← mul_assoc,videm,mul_assoc,ideal_right_fixed]⟩
  invFun x := ⟨⟨x.val,⟨x.val,corner_right_fixed μ i j x⟩⟩,by
    refine ⟨⟨x.val,⟨x.val,corner_right_fixed μ i j x⟩⟩,?_⟩
    apply Subtype.ext
    exact corner_left_fixed μ i j x⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl
end LittleFinitistic.CornerProjection

end

end OAI
