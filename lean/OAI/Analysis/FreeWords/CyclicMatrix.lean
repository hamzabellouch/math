import Mathlib

namespace OAI

noncomputable section

namespace KKLocalPatching

noncomputable section

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

def shiftMatrix (g : G) : Matrix G G ℂ := (Equiv.addRight g).permMatrix ℂ

omit [Fintype G] in
@[simp] theorem shift_zero : shiftMatrix (0:G)=1 := by
  have h : Equiv.addRight (0:G)=1 := by ext; simp [Equiv.addRight]
  simp [shiftMatrix,h]

@[simp] theorem shift_add (g h : G) : shiftMatrix (g+h)=shiftMatrix g*shiftMatrix h := by
  have he : Equiv.addRight (g+h)=(Equiv.addRight h)*(Equiv.addRight g) := by
    ext x
    simp [Equiv.addRight,add_assoc]
  rw [shiftMatrix,he,Matrix.permMatrix_mul]
  rfl

omit [Fintype G] in
@[simp] theorem shift_star (g : G) : star (shiftMatrix g)=shiftMatrix (-g) := by
  change ((Equiv.addRight g).permMatrix ℂ).conjTranspose=_
  rw [Matrix.conjTranspose_permMatrix]
  congr 1
  ext x
  simp [Equiv.addRight]

def shiftUnitary (g : G) : unitary (Matrix G G ℂ) :=
  ⟨shiftMatrix g, by
    constructor
    · rw [shift_star,← shift_add,neg_add_cancel,shift_zero]
    · rw [shift_star,← shift_add,add_neg_cancel,shift_zero]⟩

@[simp] theorem shiftUnitary_val (g:G) : (shiftUnitary g).val=shiftMatrix g := rfl

def shiftHom : Multiplicative G →* unitary (Matrix G G ℂ) where
  toFun g := shiftUnitary g.toAdd
  map_one' := Subtype.ext shift_zero
  map_mul' g h := Subtype.ext (shift_add g.toAdd h.toAdd)

@[simp] theorem shift_zsmul (k : ℤ) (g : G) : shiftUnitary (k • g)=(shiftUnitary g)^k :=
  (shiftHom : Multiplicative G →* unitary (Matrix G G ℂ)).map_zpow _ _

theorem shift_trace (g : G) (hg : g ≠ 0) : Matrix.trace (shiftMatrix g)=0 := by
  rw [shiftMatrix,Matrix.trace_permutation]
  have hf : Function.fixedPoints (Equiv.addRight g)=∅ := by
    ext x
    change (x+g=x) ↔ False
    simp only [add_eq_left]
    exact iff_false_intro hg
  rw [hf,Set.ncard_empty,Nat.cast_zero]

end

end KKLocalPatching
end

end OAI
