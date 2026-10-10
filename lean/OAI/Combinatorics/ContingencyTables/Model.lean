import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Pi
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Contingency tables with arbitrary margins

The feasible sets in result 200 are represented by natural-valued
matrices, without a positivity, balance, or sparsity restriction on
the margins. The finite encoding bound is proved rather than assumed.
-/

namespace ContingencyTables

open Finset

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The row and column equations in both papers. -/
def HasMargins (X : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) : Prop :=
  (∀ i, ∑ j, X i j = r i) ∧ (∀ j, ∑ i, X i j = c j)

/-- Unrestricted nonnegative integer tables with the specified margins. -/
def Table (r : I → ℕ) (c : J → ℕ) := {X : I → J → ℕ // HasMargins X r c}

/-- The entry constraints for the companion paper, including structural zeros. -/
def BoundedTable (r : I → ℕ) (c : J → ℕ) (b : I → J → ℕ) :=
  {X : Table r c // ∀ i j, X.val i j ≤ b i j}

theorem totals_equal {X : I → J → ℕ} {r : I → ℕ} {c : J → ℕ}
    (h : HasMargins X r c) : ∑ i, r i = ∑ j, c j := by
  simp_rw [← h.1, ← h.2]
  exact sum_comm

theorem entry_le_row {X : I → J → ℕ} {r : I → ℕ} {c : J → ℕ}
    (h : HasMargins X r c) (i : I) (j : J) : X i j ≤ r i := by
  rw [← h.1 i]
  exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)

theorem entry_le_total {X : I → J → ℕ} {r : I → ℕ} {c : J → ℕ}
    (h : HasMargins X r c) (i : I) (j : J) : X i j ≤ ∑ i, r i :=
  (entry_le_row h i j).trans (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i))

/-- Binary margins may be large, but the feasible set is finite. -/
instance table_finite (r : I → ℕ) (c : J → ℕ) : Finite (Table r c) := by
  let encode : Table r c → I → J → Fin ((∑ i, r i) + 1) :=
    fun X i j => ⟨X.val i j, Nat.lt_succ_of_le (entry_le_total X.property i j)⟩
  apply Finite.of_injective encode
  intro X Y h
  apply Subtype.ext
  funext i j
  exact congrArg Fin.val (congrFun (congrFun h i) j)

noncomputable instance table_fintype (r : I → ℕ) (c : J → ℕ) : Fintype (Table r c) :=
  Fintype.ofFinite _

noncomputable instance boundedTable_fintype (r : I → ℕ) (c : J → ℕ) (b : I → J → ℕ) :
    Fintype (BoundedTable r c b) := by
  classical
  unfold BoundedTable
  infer_instance

/-- The bound used in the exact correction's exhaustive branch. -/
theorem table_card_le (r : I → ℕ) (c : J → ℕ) :
    Fintype.card (Table r c) ≤ ((∑ i, r i) + 1) ^ (Fintype.card I * Fintype.card J) := by
  classical
  let encode : Table r c → I → J → Fin ((∑ i, r i) + 1) :=
    fun X i j => ⟨X.val i j, Nat.lt_succ_of_le (entry_le_total X.property i j)⟩
  have hinj : Function.Injective encode := by
    intro X Y h
    apply Subtype.ext
    funext i j
    exact congrArg Fin.val (congrFun (congrFun h i) j)
  have h := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_fun, Fintype.card_fin, ← pow_mul, Nat.mul_comm] using h

section Existence

variable [DecidableEq I] [DecidableEq J]

private theorem sum_decrease_one (r : I → ℕ) (i : I) (hi : 0 < r i) :
    (∑ k, Function.update r i (r i - 1) k) + 1 = ∑ k, r k := by
  rw [sum_update_of_mem (mem_univ i)]
  have hsum := sum_erase_add (univ : Finset I) r (mem_univ i)
  simp only [sdiff_singleton_eq_erase] at *
  omega

/-- Equal total nonnegative margins always admit an unrestricted table.
The proof removes one unit at a positive row and a positive column.
It is an existence argument; no polynomial runtime is asserted here. -/
theorem exists_table (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j) :
    ∃ X, HasMargins X r c := by
  suffices ∀ N (r : I → ℕ) (c : J → ℕ),
      (∑ i, r i) = N → (∑ j, c j) = N → ∃ X, HasMargins X r c by
    exact this _ r c rfl htotal.symm
  intro N
  induction N with
  | zero =>
    intro r c hr hc
    refine ⟨fun _ _ => 0, ?_, ?_⟩
    · intro i
      have hri := single_le_sum (f := r) (fun _ _ => Nat.zero_le _) (mem_univ i)
      rw [hr] at hri
      simpa using (Nat.eq_zero_of_le_zero hri).symm
    · intro j
      have hcj := single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (mem_univ j)
      rw [hc] at hcj
      simpa using (Nat.eq_zero_of_le_zero hcj).symm
  | succ N ih =>
    intro r c hr hc
    obtain ⟨i₀, _, hi₀⟩ := exists_ne_zero_of_sum_ne_zero
      (s := (univ : Finset I)) (f := r) (by rw [hr]; exact Nat.succ_ne_zero _)
    obtain ⟨j₀, _, hj₀⟩ := exists_ne_zero_of_sum_ne_zero
      (s := (univ : Finset J)) (f := c) (by rw [hc]; exact Nat.succ_ne_zero _)
    let r' := Function.update r i₀ (r i₀ - 1)
    let c' := Function.update c j₀ (c j₀ - 1)
    have hr' : ∑ i, r' i = N := by
      have h := sum_decrease_one r i₀ (Nat.pos_of_ne_zero hi₀)
      dsimp [r']
      omega
    have hc' : ∑ j, c' j = N := by
      have h := sum_decrease_one c j₀ (Nat.pos_of_ne_zero hj₀)
      dsimp [c']
      omega
    obtain ⟨X, hXr, hXc⟩ := ih r' c' hr' hc'
    refine ⟨fun i j => X i j + if i = i₀ ∧ j = j₀ then 1 else 0, ?_, ?_⟩
    · intro i
      rw [sum_add_distrib, hXr i]
      by_cases hi : i = i₀
      · subst i
        simp only [true_and, sum_ite_eq', mem_univ, ite_true, r', Function.update_self]
        omega
      · simp [hi, r']
    · intro j
      rw [sum_add_distrib, hXc j]
      by_cases hj : j = j₀
      · subst j
        simp only [and_true, sum_ite_eq', mem_univ, ite_true, c', Function.update_self]
        omega
      · simp [hj, c']

theorem table_nonempty (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j) :
    Nonempty (Table r c) := by
  obtain ⟨X, hX⟩ := exists_table r c htotal
  exact ⟨⟨X, hX⟩⟩

end Existence

end ContingencyTables

end OAI
