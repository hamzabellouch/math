import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Equiv.Sum

namespace OAI
noncomputable section
namespace ExternalTensor.Binomial

/-- A branch records the choices of the two summands during iteration. -/
def Branch : ℕ → Type
  | 0 => Unit
  | n + 1 => Branch n ⊕ Branch n

instance branchFintype : (n : ℕ) → Fintype (Branch n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => letI := branchFintype n; inferInstanceAs (Fintype (Branch n ⊕ Branch n))

def weight : {n : ℕ} → Branch n → ℕ
  | 0, _ => 0
  | _ + 1, .inl x => weight x
  | _ + 1, .inr x => weight x + 1

theorem weight_le : ∀ {n : ℕ} (x : Branch n), weight x ≤ n
  | 0, _ => Nat.le_refl _
  | _n + 1, .inl x => Nat.le_succ_of_le (weight_le x)
  | _n + 1, .inr x => Nat.succ_le_succ (weight_le x)

/-- The left branch has weight zero exactly when the old branch does. -/
def zeroFiber (n : ℕ) : {x : Branch (n+1) // weight x = 0} ≃
    {x : Branch n // weight x = 0} where
  toFun x := match x with
    | ⟨.inl x, h⟩ => ⟨x, h⟩
    | ⟨.inr x, h⟩ => False.elim (Nat.noConfusion h)
  invFun x := ⟨.inl x.val, x.property⟩
  left_inv x := by
    rcases x with ⟨x | x, h⟩
    · rfl
    · exact False.elim (Nat.noConfusion h)
  right_inv x := rfl

/-- The two disjoint ways to achieve weight q+1 give Pascal's recurrence. -/
def succFiber (n q : ℕ) : {x : Branch (n+1) // weight x = q+1} ≃
    ({x : Branch n // weight x = q+1} ⊕ {x : Branch n // weight x = q}) where
  toFun x := match x with
    | ⟨.inl x, h⟩ => .inl ⟨x, h⟩
    | ⟨.inr x, h⟩ => .inr ⟨x, Nat.succ.inj h⟩
  invFun x := match x with
    | .inl x => ⟨.inl x.val, x.property⟩
    | .inr x => ⟨.inr x.val, congrArg Nat.succ x.property⟩
  left_inv x := by rcases x with ⟨x | x, h⟩ <;> rfl
  right_inv x := by cases x <;> rfl

theorem card_weight (n q : ℕ) :
    Fintype.card {x : Branch n // weight x = q} = Nat.choose n q := by
  classical
  induction n generalizing q with
  | zero =>
    cases q with
    | zero =>
      let : Unique {x : Branch 0 // weight x = 0} :=
        ⟨⟨⟨(), rfl⟩⟩, fun x => by rcases x with ⟨⟨⟩, h⟩; rfl⟩
      simp
    | succ q =>
      let : IsEmpty {x : Branch 0 // weight x = q+1} :=
        ⟨fun x => Nat.noConfusion x.property⟩
      simp
  | succ n ih =>
    cases q with
    | zero => rw [Fintype.card_congr (zeroFiber n), ih]; simp
    | succ q => rw [Fintype.card_congr (succFiber n q), Fintype.card_sum, ih, ih,
        Nat.choose_succ_succ, Nat.add_comm]

def degree {n : ℕ} (x : Branch n) : Fin (n+1) := ⟨weight x, Nat.lt_succ_of_le (weight_le x)⟩

def degreeFiber (n : ℕ) (q : Fin (n+1)) :
    {x : Branch n // degree x = q} ≃ {x : Branch n // weight x = q.val} :=
  Equiv.subtypeEquivRight (fun _ => Fin.ext_iff)

def fiberFin (n : ℕ) (q : Fin (n+1)) :
    {x : Branch n // degree x = q} ≃ Fin (Nat.choose n q.val) := by
  classical
  exact Fintype.equivFinOfCardEq ((Fintype.card_congr (degreeFiber n q)).trans (card_weight n q))

/-- Group branches by their weight, with the binomial coefficient as the exact fiber size. -/
def groupEquiv (n : ℕ) : Branch n ≃ Σ q : Fin (n+1), Fin (Nat.choose n q.val) :=
  (Equiv.sigmaFiberEquiv (@degree n)).symm.trans (Equiv.sigmaCongrRight (fiberFin n))

@[simp] theorem groupEquiv_fst (n : ℕ) (x : Branch n) :
    (groupEquiv n x).1 = degree x := rfl
end ExternalTensor.Binomial

end

end OAI
