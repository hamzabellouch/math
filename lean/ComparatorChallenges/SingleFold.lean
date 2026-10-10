import Mathlib

namespace OAI

namespace SingleFold

/-- Evaluation over the integers of an integer polynomial at natural inputs. -/
noncomputable def evalNat {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (a : Fin n → ℕ) (w : Fin m → ℕ) : ℤ :=
  MvPolynomial.eval (Sum.elim (fun i => (a i : ℤ)) (fun j => (w j : ℤ))) P

/-- Exact existence on members, no witness on nonmembers, and uniqueness of the
whole witness on every input. No coordinates are hidden outside `w`. -/
def Represents {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (S : Set (Fin n → ℕ)) : Prop :=
  ∀ a, (a ∈ S ↔ ∃ w, evalNat P a w = 0) ∧
    ∀ w v, evalNat P a w = 0 → evalNat P a v = 0 → w = v

/-- Single-fold representation with positive input and witness lengths. -/
def MainStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (S : Set (Fin n → ℕ)), REPred (fun a => a ∈ S) →
    ∃ (m : ℕ), 1 ≤ m ∧ ∃ P : MvPolynomial (Fin n ⊕ Fin m) ℤ, Represents P S

theorem main : MainStatement := by
  sorry

end SingleFold

end OAI
