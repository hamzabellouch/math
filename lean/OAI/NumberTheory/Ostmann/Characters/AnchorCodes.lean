import Mathlib

namespace OAI

open scoped BigOperators
namespace Ostmann.Characters.AnchorCodes

abbrev ParityPath (n : ℕ) := Fin (n+1) → ℤˣ

def pair (α incoming outgoing : ℤˣ) : ℤˣ × ℤˣ :=
  if outgoing = incoming then (1, -α / incoming) else (-α / incoming, 1)

theorem pair_product (α e e' : ℤˣ) :
    (pair α e e').1 * (pair α e e').2 = -α / e := by
  unfold pair
  split_ifs <;> simp

theorem pair_incoming {α e e' f f' : ℤˣ}
    (h : pair α e e' = pair α f f') : e = f := by
  have hh := congrArg (fun z : ℤˣ × ℤˣ => z.1*z.2) h
  simpa only [pair_product, div_right_inj] using hh

def code {n : ℕ} (α : Fin n → ℤˣ) (e : ParityPath n) : Fin n → ℤˣ × ℤˣ :=
  fun j => pair (α j) (e j.castSucc) (e j.succ)

theorem incoming_of_code_eq {n : ℕ} {α : Fin n → ℤˣ} {e f : ParityPath n}
    (h : code α e = code α f) (j : Fin n) : e j.castSucc = f j.castSucc :=
  pair_incoming (congrFun h j)

theorem code_final_injective {n : ℕ} (α : Fin n → ℤˣ) :
    Function.Injective (fun e : ParityPath n => (code α e, e (Fin.last n))) := by
  intro e f h
  have hc := congrArg Prod.fst h
  have hf := congrArg Prod.snd h
  funext j
  refine Fin.lastCases hf (fun i => ?_) j
  exact incoming_of_code_eq hc i

theorem different_code_of_same_final {n : ℕ} {α : Fin n → ℤˣ}
    {e f : ParityPath n} (hne : e ≠ f) (hf : e (Fin.last n) = f (Fin.last n)) :
    code α e ≠ code α f := by
  intro hc
  exact hne (code_final_injective α (Prod.ext hc hf))

theorem card_code_fiber_le_two {n : ℕ} (α : Fin n → ℤˣ) (c : Fin n → ℤˣ × ℤˣ) :
    Fintype.card {e : ParityPath n // code α e = c} ≤ 2 := by
  classical
  calc
    _ ≤ Fintype.card ℤˣ := Fintype.card_le_of_injective
      (fun e : {e : ParityPath n // code α e = c} => e.val (Fin.last n)) (by
        intro e f h
        apply Subtype.ext
        exact code_final_injective α (Prod.ext (e.property.trans f.property.symm) h))
    _ = 2 := Fintype.card_units_int

theorem card_code_slots_le {n m : ℕ} (α : Fin n → ℤˣ)
    (c : Fin n → ℤˣ × ℤˣ) :
    Fintype.card ({e : ParityPath n // code α e = c} × Fin m) ≤ 2*m := by
  rw [Fintype.card_prod, Fintype.card_fin]
  exact Nat.mul_le_mul_right m (card_code_fiber_le_two α c)
end Ostmann.Characters.AnchorCodes

end OAI
