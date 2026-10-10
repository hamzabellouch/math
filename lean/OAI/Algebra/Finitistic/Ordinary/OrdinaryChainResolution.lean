import OAI.Algebra.Finitistic.Ordinary.OrdinaryChainAlgebra
import OAI.Algebra.Finitistic.Tensor.IdempotentTensor
import Mathlib.Algebra.Module.Projective

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k : Type u} [Field k] {l : ℕ}
namespace ChainAlgebra

@[simp] theorem arrow_mul (i : Fin l) (x : ChainAlgebra k l) :
    arrow k l i * x = x.1 i.castSucc • arrow k l i := by
  apply Prod.ext <;> funext j
  · change (0:k) * x.1 j = x.1 i.castSucc * 0
    simp
  · change 0 * x.2 j + (Pi.single i 1 : Fin l → k) j * x.1 j.castSucc =
      x.1 i.castSucc * (Pi.single i 1 : Fin l → k) j
    by_cases h : j = i <;> simp [h]

@[simp] theorem smul_diagonal (c : k) (x : ChainAlgebra k l) (i : Fin (l+1)) :
    (c • x).1 i = c * x.1 i := rfl
@[simp] theorem smul_radical (c : k) (x : ChainAlgebra k l) (i : Fin l) :
    (c • x).2 i = c * x.2 i := rfl
@[simp] theorem vertex_diagonal (i j : Fin (l+1)) :
    (vertex k l i).1 j = (Pi.single i 1 : Fin (l+1) → k) j := rfl
@[simp] theorem arrow_diagonal (i : Fin l) (j : Fin (l+1)) :
    (arrow k l i).1 j = 0 := rfl
@[simp] theorem arrow_radical (i j : Fin l) :
    (arrow k l i).2 j = (Pi.single i 1 : Fin l → k) j := rfl

/-- The two displayed coordinates of each noninitial right projective. -/
theorem vertex_succ_mul (i : Fin l) (x : ChainAlgebra k l) :
    vertex k l i.succ * x = x.1 i.succ • vertex k l i.succ + x.2 i • arrow k l i := by
  rw [add_eq, smul_eq, smul_eq]
  apply Prod.ext <;> funext j
  · change (Pi.single i.succ 1 : Fin (l+1) → k) j * x.1 j =
      x.1 i.succ * (Pi.single i.succ 1 : Fin (l+1) → k) j + x.2 i * 0
    by_cases h : j = i.succ <;> simp [h]
  · change (Pi.single i.succ 1 : Fin (l+1) → k) j.succ * x.2 j + 0 * x.1 j.castSucc =
      x.1 i.succ * 0 + x.2 i * (Pi.single i 1 : Fin l → k) j
    by_cases h : j = i
    · subst j; simp
    · have hs : j.succ ≠ i.succ := fun e => h (Fin.succ_injective _ e)
      simp [h, hs]

/-- The initial projective has no radical coordinate. -/
theorem vertex_zero_mul (x : ChainAlgebra k l) :
    vertex k l 0 * x = x.1 0 • vertex k l 0 := by
  rw [smul_eq]
  apply Prod.ext <;> funext j
  · change (Pi.single 0 1 : Fin (l+1) → k) j * x.1 j =
      x.1 0 * (Pi.single 0 1 : Fin (l+1) → k) j
    by_cases h : j = 0 <;> simp [h]
  · change (Pi.single 0 1 : Fin (l+1) → k) j.succ * x.2 j + 0 * x.1 j.castSucc = x.1 0 * 0
    simp

/-- Actual right projectives in the source resolution. -/
abbrev rightTerm (i : Fin (l+1)) := IdempotentTensor.rightIdeal (vertex k l i)

def leftMultiply (x : ChainAlgebra k l) : ChainAlgebra k l →ₗ[(ChainAlgebra k l)ᵐᵒᵖ] ChainAlgebra k l where
  toFun y := x*y
  map_add' := mul_add x
  map_smul' r y := (mul_assoc x y r.unop).symm

def retract (i : Fin (l+1)) : ChainAlgebra k l →ₗ[(ChainAlgebra k l)ᵐᵒᵖ] rightTerm (k := k) i :=
  (leftMultiply (vertex k l i)).codRestrict _ (fun x => by
    change vertex k l i * (vertex k l i * x) = vertex k l i * x
    rw [← mul_assoc, vertex_idempotent])

def rightRegularEquiv : (ChainAlgebra k l)ᵐᵒᵖ ≃ₗ[(ChainAlgebra k l)ᵐᵒᵖ] ChainAlgebra k l where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rightTerm_projective (i : Fin (l+1)) :
    Module.Projective (ChainAlgebra k l)ᵐᵒᵖ (rightTerm (k := k) i) := by
  let : Module.Projective (ChainAlgebra k l)ᵐᵒᵖ (ChainAlgebra k l) := Module.Projective.of_equiv rightRegularEquiv
  apply Module.Projective.of_split (rightTerm (k := k) i).subtype (retract i)
  ext x
  exact x.property

/-- The differential is actual left multiplication by the source arrow. -/
def resolutionMap (i : Fin l) : rightTerm (k := k) i.castSucc →ₗ[(ChainAlgebra k l)ᵐᵒᵖ] rightTerm (k := k) i.succ :=
  ((leftMultiply (arrow k l i)).comp (rightTerm (k := k) i.castSucc).subtype).codRestrict _ (fun x => by
    change vertex k l i.succ * (arrow k l i * x.val) = arrow k l i * x.val
    rw [← mul_assoc, vertex_target_arrow])

@[simp] theorem resolutionMap_value (i : Fin l) (x : rightTerm (k := k) i.castSucc) :
    (resolutionMap (k := k) i x).val = x.val.1 i.castSucc • arrow k l i := arrow_mul i x.val

/-- This is the explicit two-coordinate expansion, not a dimension argument. -/
theorem rightTerm_succ_expansion (i : Fin l) (x : rightTerm (k := k) i.succ) :
    x.val = x.val.1 i.succ • vertex k l i.succ + x.val.2 i • arrow k l i := by
  rw [← vertex_succ_mul]
  exact x.property.symm

/-- The source's resolution differentials square to zero. -/
theorem resolutionMap_square (i : ℕ) (hi : i+1 < l) :
    (resolutionMap (k := k) (⟨i+1,hi⟩ : Fin l)).comp
      (resolutionMap (k := k) (⟨i,by omega⟩ : Fin l)) = 0 := by
  ext x
  change arrow k l ⟨i+1,hi⟩ * (arrow k l ⟨i,by omega⟩ * x.val) = 0
  rw [← mul_assoc, arrow_mul_arrow, zero_mul]

theorem resolutionMap_zero_iff (i : Fin l) (x : rightTerm (k := k) i.castSucc) :
    resolutionMap (k := k) i x = 0 ↔ x.val.1 i.castSucc = 0 := by
  constructor
  · intro h
    have hr := congrArg (fun y : rightTerm (k := k) i.succ => y.val.2 i) h
    rw [resolutionMap_value, smul_radical, arrow_radical] at hr
    simpa using hr
  · intro h
    apply Subtype.ext
    rw [resolutionMap_value, h, zero_smul]
    rfl

/-- Exact description of the image: the one-dimensional radical in the next term. -/
theorem resolutionMap_range (i : Fin l) (x : rightTerm (k := k) i.succ) :
    (∃ y, resolutionMap (k := k) i y = x) ↔ x.val.1 i.succ = 0 := by
  constructor
  · rintro ⟨y,rfl⟩
    rw [resolutionMap_value, smul_diagonal, arrow_diagonal, mul_zero]
  · intro hx
    let y : rightTerm (k := k) i.castSucc := ⟨x.val.2 i • vertex k l i.castSucc, by
      change vertex k l i.castSucc * (x.val.2 i • vertex k l i.castSucc) =
        x.val.2 i • vertex k l i.castSucc
      rw [mul_smul_comm, vertex_idempotent]⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    rw [resolutionMap_value]
    have hy : y.val.1 i.castSucc = x.val.2 i := by
      dsimp [y]
      simp
    rw [hy]
    have he := rightTerm_succ_expansion i x
    rw [hx, zero_smul, zero_add] at he
    exact he.symm

/-- Exactness at every interior projective, with no assumed resolution predicate. -/
theorem resolution_exact (i : ℕ) (hi : i+1 < l)
    (x : rightTerm (k := k) (⟨i+1,by omega⟩ : Fin (l+1))) :
    resolutionMap (k := k) (⟨i+1,hi⟩ : Fin l) x = 0 ↔
      ∃ y : rightTerm (k := k) (⟨i,by omega⟩ : Fin (l+1)), resolutionMap (k := k) (⟨i,by omega⟩ : Fin l) y = x := by
  exact (resolutionMap_zero_iff (⟨i+1,hi⟩ : Fin l) x).trans
    (resolutionMap_range (⟨i,by omega⟩ : Fin l) x).symm

/-- Injectivity of the first nonzero differential in the resolution. -/
theorem resolution_first_injective (hl : 0 < l) :
    Function.Injective (resolutionMap (k := k) (⟨0,hl⟩ : Fin l)) := by
  intro x y hxy
  have hx : resolutionMap (k := k) (⟨0,hl⟩ : Fin l) (x-y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hz := (resolutionMap_zero_iff _ (x-y)).mp hx
  have he := vertex_zero_mul (x-y).val
  have hp : vertex k l 0 * (x-y).val = (x-y).val := (x-y).property
  change (x-y).val.1 0 = 0 at hz
  rw [hp, hz, zero_smul] at he
  have hsub : x-y = 0 := Subtype.ext he
  exact sub_eq_zero.mp hsub
end ChainAlgebra
end LittleFinitistic.OrdinarySimulation

end

end OAI
