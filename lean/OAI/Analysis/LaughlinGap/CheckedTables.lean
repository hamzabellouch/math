import Mathlib

namespace OAI

/-! Checked Tables. -/

noncomputable section


namespace LaughlinGap.Arithmetic

def checkMatrix {n m : ℕ} {α : Type*} [DecidableEq α]
    (A B : Fin n → Fin m → α) : Bool :=
  (List.finRange n).all fun i => (List.finRange m).all fun j => decide (A i j = B i j)

lemma checkMatrix_sound {n m : ℕ} {α : Type*} [DecidableEq α]
    (A B : Fin n → Fin m → α) (h : checkMatrix A B = true) : ∀ i j, A i j = B i j := by
  intro i j
  unfold checkMatrix at h
  have hh := List.all_eq_true.mp h i (List.mem_finRange i)
  exact of_decide_eq_true (List.all_eq_true.mp hh j (List.mem_finRange j))

end LaughlinGap.Arithmetic

namespace LaughlinGap.Arithmetic

def checkVector {n : ℕ} {α : Type*} [DecidableEq α]
    (A B : Fin n → α) : Bool :=
  (List.finRange n).all fun i => decide (A i = B i)

lemma checkVector_sound {n : ℕ} {α : Type*} [DecidableEq α]
    (A B : Fin n → α) (h : checkVector A B = true) : ∀ i, A i = B i := by
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

end LaughlinGap.Arithmetic

end

end OAI
