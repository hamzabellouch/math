import OAI.NumberTheory.Ostmann.Characters.AnchorCodes

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters

abbrev PathsOfParity (n : ℕ) (ε : ℤˣ) :=
  {t : Fin (n+1) → ℤˣ // ∏ i, t i = ε}

def pathsOfParityEquiv (n : ℕ) (ε : ℤˣ) : PathsOfParity n ε ≃ (Fin n → ℤˣ) where
  toFun t := fun i => t.val i.succ
  invFun t := ⟨Fin.cons (ε / ∏ i, t i) t, by
    rw [Fin.prod_univ_succ]
    simp⟩
  left_inv t := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    have ht := t.property
    rw [Fin.prod_univ_succ] at ht
    change ε / (∏ i : Fin n, t.val i.succ) = t.val 0
    calc
      _ = (t.val 0 * ∏ i : Fin n, t.val i.succ) /
          (∏ i : Fin n, t.val i.succ) := congrArg (fun z : ℤˣ => z /
            (∏ i : Fin n, t.val i.succ)) ht.symm
      _ = _ := mul_div_cancel_right _ _
  right_inv t := rfl

theorem card_pathsOfParity (n : ℕ) (ε : ℤˣ) :
    Fintype.card (PathsOfParity n ε) = 2^n := by
  rw [Fintype.card_congr (pathsOfParityEquiv n ε), Fintype.card_fun,
    Fintype.card_units_int, Fintype.card_fin]

noncomputable instance (n : ℕ) (ε : ℤˣ) : DecidableEq (PathsOfParity n ε) :=
  Classical.decEq _

abbrev ParityReassignments (n m : ℕ) :=
  Fin m → Equiv.Perm (PathsOfParity n 1) × Equiv.Perm (PathsOfParity n (-1))

theorem card_parityReassignments (n m : ℕ) :
    Fintype.card (ParityReassignments n m) = ((Nat.factorial (2^n))^2)^m := by
  simp only [ParityReassignments, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_perm, card_pathsOfParity, Fintype.card_fin, pow_two]
end Ostmann.Characters

end

end OAI
