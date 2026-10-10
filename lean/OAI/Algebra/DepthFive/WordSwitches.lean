import Mathlib

namespace OAI

/-! Boolean words are uniquely specified by their initial bit and their switches.
This gives the exact binomial count used in the path-type sum. -/

open scoped BigOperators

namespace Problem335
namespace WordSwitches

/-- Internal positions where adjacent bits differ. A word has `n + 1` letters. -/
def switches {n : ℕ} (w : Fin (n + 1) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => w i.castSucc ≠ w i.succ

@[simp] theorem mem_switches {n : ℕ} (w : Fin (n + 1) → Bool) (i : Fin n) :
    i ∈ switches w ↔ w i.castSucc ≠ w i.succ := by
  simp [switches]

/-- The initial letter and switch set encode a nonempty word. -/
def encode {n : ℕ} (w : Fin (n + 1) → Bool) : Bool × Finset (Fin n) :=
  (w 0, switches w)

private theorem bool_eq_of_ne_iff (a b c : Bool)
    (h : a ≠ b ↔ a ≠ c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem encode_injective (n : ℕ) :
    Function.Injective (@encode n) := by
  intro w v h
  have hzero : w 0 = v 0 := congrArg Prod.fst h
  have hs : switches w = switches v := congrArg Prod.snd h
  funext i
  induction i using Fin.induction with
  | zero => exact hzero
  | succ i ih =>
      have hi : w i.castSucc ≠ w i.succ ↔ v i.castSucc ≠ v i.succ := by
        rw [← mem_switches, ← mem_switches, hs]
      rw [ih] at hi
      exact bool_eq_of_ne_iff _ _ _ hi

/-- Every initial letter and set of switch positions specifies exactly one word. -/
theorem encode_bijective (n : ℕ) : Function.Bijective (@encode n) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨encode_injective n, ?_⟩
  simp [pow_succ, Nat.mul_comm]

noncomputable def wordEquiv (n : ℕ) :
    (Fin (n + 1) → Bool) ≃ Bool × Finset (Fin n) :=
  Equiv.ofBijective encode (encode_bijective n)

@[simp] theorem wordEquiv_apply (n : ℕ) (w : Fin (n + 1) → Bool) :
    wordEquiv n w = (w 0, switches w) := rfl

/-- The switch-count restriction of the word encoding. -/
noncomputable def countEquiv (n j : ℕ) :
    {w : Fin (n + 1) → Bool // (switches w).card = j} ≃
      Bool × {s : Finset (Fin n) // s.card = j} :=
  ((wordEquiv n).subtypeEquiv (p := fun w => (switches w).card = j)
    (q := fun p => p.2.card = j) (fun _ => Iff.rfl)).trans
    { toFun := fun p => (p.val.1, ⟨p.val.2, p.property⟩)
      invFun := fun p => ⟨(p.1, p.2.val), p.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Exactly `2 * choose n j` words of length `n + 1` have `j` switches. -/
theorem card_words_with_switches (n j : ℕ) :
    Fintype.card {w : Fin (n + 1) → Bool // (switches w).card = j} =
      2 * n.choose j := by
  rw [Fintype.card_congr (countEquiv n j), Fintype.card_prod,
    Fintype.card_bool, Fintype.card_finset_len, Fintype.card_fin]

/-- The switch-count generating function. -/
theorem sum_pow_switches {R : Type*} [CommSemiring R] (n : ℕ) (x : R) :
    (∑ w : Fin (n + 1) → Bool, x ^ (switches w).card) =
      2 * (1 + x) ^ n := by
  calc
    _ = ∑ p : Bool × Finset (Fin n), x ^ p.2.card :=
      Fintype.sum_equiv (wordEquiv n) _ _ (fun _ => rfl)
    _ = 2 * ∑ s : Finset (Fin n), x ^ s.card := by
      rw [Fintype.sum_prod_type]
      simp [two_mul]
    _ = 2 * (1 + x) ^ n := by
      congr 1
      simpa using (Finset.prod_one_add (f := fun _ : Fin n => x) Finset.univ).symm

/-- An exponential upper bound for a switch-penalized word sum. -/
theorem sum_pow_switches_le_exp (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (∑ w : Fin (n + 1) → Bool, x ^ (switches w).card) ≤
      2 * Real.exp ((n : ℝ) * x) := by
  rw [sum_pow_switches]
  have h : (1 + x) ^ n ≤ (Real.exp x) ^ n := by
    gcongr
    simpa [add_comm] using Real.add_one_le_exp x
  calc
    2 * (1 + x) ^ n ≤ 2 * (Real.exp x) ^ n := by gcongr
    _ = 2 * Real.exp ((n : ℝ) * x) := by rw [Real.exp_nat_mul]

end WordSwitches
end Problem335

end OAI
