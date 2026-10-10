import OAI.Combinatorics.BinaryEdit.FiniteVectors

namespace OAI

/-! Coordinate restrictions of the finite subtree vectors. -/

namespace TreeEdit.BinaryLower.FiniteVectors

variable {m k : ℕ}

/-- On a child's subtree the parent's cheap vector equals that child's
 distinguished vector. -/
theorem u_on_child (p : Fin k → Fin m → ℕ) (j : ℕ) (hj : j < k)
    (a b : Leaf m k) (i : Fin m)
    (hab : Agrees (j + 1) (Function.update a ⟨j, hj⟩ i) b) :
    u p j a b = w p (j + 1) (Function.update a ⟨j, hj⟩ i) b := by
  have hp := ((agrees_child_iff j hj a b i).1 hab).1
  simp [u, w, hp, hab]

/-- The parent's distinguished vector restricts to `R` times the child's. -/
theorem w_on_child (p : Fin k → Fin m → ℕ) (j : ℕ) (hj : j < k)
    (a b : Leaf m k) (i : Fin m)
    (hab : Agrees (j + 1) (Function.update a ⟨j, hj⟩ i) b) :
    w p j a b = levelProduct p ⟨j, hj⟩ •
      w p (j + 1) (Function.update a ⟨j, hj⟩ i) b := by
  have h := congrFun (w_eq_level_nsmul_u p j hj a) b
  simpa [u_on_child p j hj a b i hab] using h

@[simp] theorem u_off_subtree (p : Fin k → Fin m → ℕ) (j : ℕ)
    (a b : Leaf m k) (hab : ¬ Agrees j a b) : u p j a b = 0 := by
  simp [u, hab]

@[simp] theorem w_off_subtree (p : Fin k → Fin m → ℕ) (j : ℕ)
    (a b : Leaf m k) (hab : ¬ Agrees j a b) : w p j a b = 0 := by
  simp [w, hab]

/-- A leaf coordinate outside a subtree is fixed by every integer multiple
of its cheap vector. -/
theorem translate_u_off_subtree (p : Fin k → Fin m → ℕ) (j : ℕ)
    (a b : Leaf m k) (hab : ¬ Agrees j a b) (x : State p) (t : ℤ) :
    (x + t • u p j a) b = x b := by
  simp [u, hab]

/-- The same support statement for the distinguished vector. -/
theorem translate_w_off_subtree (p : Fin k → Fin m → ℕ) (j : ℕ)
    (a b : Leaf m k) (hab : ¬ Agrees j a b) (x : State p) (t : ℤ) :
    (x + t • w p j a) b = x b := by
  simp [w, hab]

end TreeEdit.BinaryLower.FiniteVectors

end OAI
