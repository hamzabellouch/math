import OAI.Combinatorics.ContingencyTables.Sampling.SmallEntries

namespace OAI

/-!
# Repair of a defect with its large completion

The two full matrices give the row and column views, agreeing at all
large cells. Moving one unit from the positive cell to the crossing cell
and resetting the column view preserves the enlarged margins. This is the
joint-object injection underlying the repair in paper 200-01.
-/

namespace ContingencyTables

open Finset

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- A single unit transfer, allowing source and receiver to coincide. -/
def transferInt (X : I → J → ℕ) (source receiver : I × J) (i : I) (j : J) : ℤ :=
  X i j - (if i = source.1 ∧ j = source.2 then 1 else 0) +
    (if i = receiver.1 ∧ j = receiver.2 then 1 else 0)

omit [Fintype I] [Fintype J] in
theorem transferInt_nonnegative (X : I → J → ℕ) (source receiver : I × J)
    (hsource : 0 < X source.1 source.2) (i : I) (j : J) :
    0 ≤ transferInt X source receiver i j := by
  by_cases h : i = source.1 ∧ j = source.2
  · obtain ⟨rfl, rfl⟩ := h
    simp only [transferInt, and_self, ite_true]
    split_ifs <;> omega
  · simp only [transferInt, h, ite_false, sub_zero]
    split_ifs <;> omega

omit [Fintype I] in
theorem transferInt_row (X : I → J → ℕ) (source receiver : I × J) (i : I) :
    ∑ j, transferInt X source receiver i j = (∑ j, (X i j : ℤ)) -
      (if i = source.1 then 1 else 0) + (if i = receiver.1 then 1 else 0) := by
  simp only [transferInt, sum_add_distrib, sum_sub_distrib, ite_and]
  simp

omit [Fintype J] in
theorem transferInt_column (X : I → J → ℕ) (source receiver : I × J) (j : J) :
    ∑ i, transferInt X source receiver i j = (∑ i, (X i j : ℤ)) -
      (if j = source.2 then 1 else 0) + (if j = receiver.2 then 1 else 0) := by
  have h (i : I) (p : I × J) : (i = p.1 ∧ j = p.2) ↔ (j = p.2 ∧ i = p.1) := and_comm
  simp only [transferInt, sum_add_distrib, sum_sub_distrib, h, ite_and]
  simp

/-- The defect equation `q=x-e_t+e_s` identifies the sign convention. -/
def IsDefect (x q : I → J → ℕ) (negative positive : I × J) : Prop :=
  negative ≠ positive ∧
    ∀ i j, (q i j : ℤ) = transferInt x positive negative i j

omit [Fintype I] [Fintype J] in
theorem IsDefect.positive_entry {x q : I → J → ℕ} {s t : I × J}
    (h : IsDefect x q s t) : 0 < x t.1 t.2 := by
  have hst : ¬(t.1 = s.1 ∧ t.2 = s.2) := by
    rintro ⟨h₁, h₂⟩
    exact h.1 (Prod.ext h₁.symm h₂.symm)
  have heq := h.2 t.1 t.2
  simp only [transferInt, and_self, ite_true, hst, ite_false, add_zero] at heq
  omega

/-- The crossing receiver `(i',j)` in the manuscript. -/
def repairMatrix (x : I → J → ℕ) (s t : I × J) : I → J → ℕ :=
  fun i j => (transferInt x t (t.1, s.2) i j).toNat

omit [Fintype I] [Fintype J] in
theorem repairMatrix_cast {x q : I → J → ℕ} {s t : I × J}
    (h : IsDefect x q s t) (i : I) (j : J) :
    (repairMatrix x s t i j : ℤ) = transferInt x t (t.1, s.2) i j :=
  Int.toNat_of_nonneg (transferInt_nonnegative x t (t.1, s.2) h.positive_entry i j)

/-- The repaired matrix has the old row totals and old column-view totals.
The crossing cell may be large, and either of its coordinates may coincide
with those of the original defect cells. -/
theorem repairMatrix_margins {x q : I → J → ℕ} {s t : I × J}
    (h : IsDefect x q s t) (r : I → ℕ) (c : J → ℕ)
    (hr : ∀ i, ∑ j, x i j = r i) (hc : ∀ j, ∑ i, q i j = c j) :
    HasMargins (repairMatrix x s t) r c := by
  constructor
  · intro i
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [repairMatrix_cast h]
    rw [transferInt_row]
    simp only [sub_add_cancel, ← Nat.cast_sum, hr]
  · intro j
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [repairMatrix_cast h]
    rw [transferInt_column]
    have hcol : (∑ i, (q i j : ℤ)) = ∑ i, transferInt x t s i j := by
      apply sum_congr rfl
      intro i _
      exact h.2 i j
    rw [transferInt_column, ← Nat.cast_sum, hc] at hcol
    exact hcol.symm

omit [Fintype I] [Fintype J] in
/-- Fixed defect labels make the repair injective on joint row/column
views, hence also on the state together with its large completion. -/
theorem repairMatrix_injective {x q y p : I → J → ℕ} {s t : I × J}
    (hx : IsDefect x q s t) (hy : IsDefect y p s t)
    (heq : repairMatrix x s t = repairMatrix y s t) : x = y ∧ q = p := by
  have hxy : x = y := by
    funext i j
    have h := congrArg (fun X : I → J → ℕ => (X i j : ℤ)) heq
    rw [repairMatrix_cast hx, repairMatrix_cast hy] at h
    simp only [transferInt] at h
    exact Int.natCast_inj.mp (by omega)
  refine ⟨hxy, ?_⟩
  funext i j
  apply Int.natCast_inj.mp
  rw [hx.2, hy.2, hxy]

end ContingencyTables

end OAI
