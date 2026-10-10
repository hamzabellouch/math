import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.FinCases
import OAI.Algebra.Finitistic.Encoding.QuadraticEncoding

namespace OAI

namespace LittleFinitistic.CornerSpaces
open ThreeVertexAlgebra

universe u
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)

/-- The actual two-sided corner e_i B e_j as a vector subspace. -/
def corner (i j : Fin 3) : Submodule k (ThreeVertexAlgebra μ) where
  carrier := {x | vertex μ i * x * vertex μ j = x}
  zero_mem' := by
    change vertex μ i * (0 : ThreeVertexAlgebra μ) * vertex μ j = 0
    rw [mul_zero,zero_mul]
  add_mem' := by
    intro x y hx hy
    change vertex μ i * x * vertex μ j = x at hx
    change vertex μ i * y * vertex μ j = y at hy
    change vertex μ i * (x+y) * vertex μ j = x+y
    rw [mul_add,add_mul,hx,hy]
  smul_mem' := by
    intro r x hx
    change vertex μ i * x * vertex μ j = x at hx
    change vertex μ i * (r • x) * vertex μ j = r • x
    rw [mul_smul_comm,smul_mul_assoc,hx]

noncomputable def corner10Equiv : corner μ 1 0 ≃ₗ[k] V where
  toFun x := x.val.2.2.2.1
  invFun v := ⟨(0,0,0,v,0,0),by
    change mul μ (mul μ (vertex μ 1) (0,0,0,v,0,0)) (vertex μ 0) = _
    simp [vertex,mul]⟩
  left_inv x := by
    apply Subtype.ext
    have hx := x.property
    change mul μ (mul μ (vertex μ 1) x.val) (vertex μ 0) = x.val at hx
    simpa [vertex,mul] using hx
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def corner21Equiv : corner μ 2 1 ≃ₗ[k] W where
  toFun x := x.val.2.2.2.2.1
  invFun w := ⟨(0,0,0,0,w,0),by
    change mul μ (mul μ (vertex μ 2) (0,0,0,0,w,0)) (vertex μ 1) = _
    simp [vertex,mul]⟩
  left_inv x := by
    apply Subtype.ext
    have hx := x.property
    change mul μ (mul μ (vertex μ 2) x.val) (vertex μ 1) = x.val at hx
    simpa [vertex,mul] using hx
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def corner20Equiv : corner μ 2 0 ≃ₗ[k] U where
  toFun x := x.val.2.2.2.2.2
  invFun u := ⟨(0,0,0,0,0,u),by
    change mul μ (mul μ (vertex μ 2) (0,0,0,0,0,u)) (vertex μ 0) = _
    simp [vertex,mul]⟩
  left_inv x := by
    apply Subtype.ext
    have hx := x.property
    change mul μ (mul μ (vertex μ 2) x.val) (vertex μ 0) = x.val at hx
    simpa [vertex,mul] using hx
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A diagonal corner has only its scalar trivial path. -/
noncomputable def diagonalEquiv (i : Fin 3) : corner μ i i ≃ₗ[k] k where
  toFun x := if i = 0 then x.val.1 else if i = 1 then x.val.2.1 else x.val.2.2.1
  invFun c := ⟨c • vertex μ i,by
    change vertex μ i * (c • vertex μ i) * vertex μ i = c • vertex μ i
    rw [mul_smul_comm,smul_mul_assoc]
    have hi := (directedSystem μ).idem i
    change vertex μ i * vertex μ i = vertex μ i at hi
    rw [hi,hi]⟩
  left_inv x := by
    apply Subtype.ext
    have hx := x.property
    change mul μ (mul μ (vertex μ i) x.val) (vertex μ i) = x.val at hx
    fin_cases i <;> simpa [vertex,mul,smul_eq μ] using hx
  right_inv c := by fin_cases i <;> simp [vertex,smul_eq μ]
  map_add' x y := by fin_cases i <;> rfl
  map_smul' c x := by fin_cases i <;> rfl

/-- No path points backwards in the actual algebra. -/
theorem corner_zero_of_lt (i j : Fin 3) (hij : i < j) (x : corner μ i j) : x = 0 := by
  apply Subtype.ext
  have hx := x.property
  change (directedSystem μ).e i * x.val * (directedSystem μ).e j = x.val at hx
  rw [(directedSystem μ).directed j i hij x.val] at hx
  exact hx.symm
end LittleFinitistic.CornerSpaces

end OAI
