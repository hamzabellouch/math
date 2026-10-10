import OAI.Combinatorics.ContingencyTables.Model
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic

namespace OAI

/-!
# Four-cycle moves for the small-entry estimate

The move raises the marked cell, lowers one donor in its row and one in
its column, and raises the opposite corner. No upper cell bound is used.
-/

namespace ContingencyTables

open Finset

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The signed four-cycle update, before converting back to natural entries. -/
def fourCycleInt (X : I → J → ℕ) (a b : I) (s t : J) (v : ℕ) (i : I) (j : J) : ℤ :=
  X i j + ((if i = a then 1 else 0) - (if i = b then 1 else 0)) *
    ((if j = s then 1 else 0) - (if j = t then 1 else 0)) * v

omit [Fintype I] [Fintype J] in
theorem fourCycleInt_nonnegative (X : I → J → ℕ) (a b : I) (s t : J) (v : ℕ)
    (hab : a ≠ b) (hst : s ≠ t) (hrow : v ≤ X a t) (hcol : v ≤ X b s)
    (i : I) (j : J) : 0 ≤ fourCycleInt X a b s t v i j := by
  by_cases hi : i = a
  · subst i
    by_cases hj : j = s
    · subst j
      simp [fourCycleInt, hab, hst]
      omega
    · by_cases hj' : j = t
      · subst j
        simp [fourCycleInt, hab, Ne.symm hst]
        omega
      · simp [fourCycleInt, hab, hj, hj']
  · by_cases hi' : i = b
    · subst i
      by_cases hj : j = s
      · subst j
        simp [fourCycleInt, Ne.symm hab, hst]
        omega
      · by_cases hj' : j = t
        · subst j
          simp [fourCycleInt, Ne.symm hab, Ne.symm hst]
          omega
        · simp [fourCycleInt, Ne.symm hab, hj, hj']
    · simp [fourCycleInt, hi, hi']

omit [Fintype I] in
theorem fourCycleInt_rows (X : I → J → ℕ) (a b : I) (s t : J) (v : ℕ) (i : I) :
    ∑ j, fourCycleInt X a b s t v i j = ∑ j, (X i j : ℤ) := by
  simp only [fourCycleInt, sum_add_distrib, ← sum_mul, ← mul_sum, sum_sub_distrib]
  simp

omit [Fintype J] in
theorem fourCycleInt_columns (X : I → J → ℕ) (a b : I) (s t : J) (v : ℕ) (j : J) :
    ∑ i, fourCycleInt X a b s t v i j = ∑ i, (X i j : ℤ) := by
  simp only [fourCycleInt, sum_add_distrib, ← sum_mul, sum_sub_distrib]
  simp

/-- A nonnegative four-cycle is again a table with precisely the same margins. -/
def fourCycle {r : I → ℕ} {c : J → ℕ} (X : Table r c)
    (a b : I) (s t : J) (v : ℕ) (hab : a ≠ b) (hst : s ≠ t)
    (hrow : v ≤ X.val a t) (hcol : v ≤ X.val b s) : Table r c := by
  let Y := fun i j => (fourCycleInt X.val a b s t v i j).toNat
  have hcast (i : I) (j : J) : (Y i j : ℤ) = fourCycleInt X.val a b s t v i j :=
    Int.toNat_of_nonneg (fourCycleInt_nonnegative X.val a b s t v hab hst hrow hcol i j)
  refine ⟨Y, ?_, ?_⟩
  · intro i
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [hcast]
    rw [fourCycleInt_rows, ← Nat.cast_sum, X.property.1 i]
  · intro j
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [hcast]
    rw [fourCycleInt_columns, ← Nat.cast_sum, X.property.2 j]

@[simp] theorem fourCycle_cast {r : I → ℕ} {c : J → ℕ} (X : Table r c)
    (a b : I) (s t : J) (v : ℕ) (hab : a ≠ b) (hst : s ≠ t)
    (hrow : v ≤ X.val a t) (hcol : v ≤ X.val b s) (i : I) (j : J) :
    ((fourCycle X a b s t v hab hst hrow hcol).val i j : ℤ) =
      fourCycleInt X.val a b s t v i j :=
  Int.toNat_of_nonneg (fourCycleInt_nonnegative X.val a b s t v hab hst hrow hcol i j)

@[simp] theorem fourCycle_marked {r : I → ℕ} {c : J → ℕ} (X : Table r c)
    (a b : I) (s t : J) (v : ℕ) (hab : a ≠ b) (hst : s ≠ t)
    (hrow : v ≤ X.val a t) (hcol : v ≤ X.val b s) :
    (fourCycle X a b s t v hab hst hrow hcol).val a s = X.val a s + v := by
  apply Int.natCast_inj.mp
  rw [fourCycle_cast]
  simp [fourCycleInt, hab, hst]

/-- With the donor labels and step fixed, the target determines the source. -/
theorem fourCycle_injective {r : I → ℕ} {c : J → ℕ}
    (X Y : Table r c) (a b : I) (s t : J) (v : ℕ) (hab : a ≠ b) (hst : s ≠ t)
    (hXrow : v ≤ X.val a t) (hXcol : v ≤ X.val b s)
    (hYrow : v ≤ Y.val a t) (hYcol : v ≤ Y.val b s)
    (heq : fourCycle X a b s t v hab hst hXrow hXcol =
      fourCycle Y a b s t v hab hst hYrow hYcol) : X = Y := by
  apply Subtype.ext
  funext i j
  have h := congrArg (fun Z : Table r c => (Z.val i j : ℤ)) heq
  simp only [fourCycle_cast, fourCycleInt] at h
  exact Int.natCast_inj.mp (add_right_cancel h)

/-- Double counting the four-cycle moves. The source marked value and two
donor labels suffice to reverse a move: the target marked value determines
the step. The donor-existence condition is separated from the injection so
that the margin estimate can be checked independently. -/
theorem small_entry_count_of_donors {r : I → ℕ} {c : J → ℕ}
    (a : I) (s : J) (t V : ℕ)
    (hdonors : ∀ X : Table r c, X.val a s < t →
      ∃ p : I × J, a ≠ p.1 ∧ s ≠ p.2 ∧ V ≤ X.val a p.2 ∧ V ≤ X.val p.1 s) :
    Fintype.card {X : Table r c // X.val a s < t} * V ≤
      Fintype.card (Table r c) * (Fintype.card I * Fintype.card J * t) := by
  classical
  let Bad := {X : Table r c // X.val a s < t}
  let donor (X : Bad) : I × J := Classical.choose (hdonors X.val X.property)
  have hdonor (X : Bad) : a ≠ (donor X).1 ∧ s ≠ (donor X).2 ∧
      V ≤ X.val.val a (donor X).2 ∧ V ≤ X.val.val (donor X).1 s :=
    Classical.choose_spec (hdonors X.val X.property)
  let next (X : Bad) (v : Fin V) : Table r c :=
    fourCycle X.val a (donor X).1 s (donor X).2 (v.val + 1)
      (hdonor X).1 (hdonor X).2.1
      ((Nat.succ_le_of_lt v.isLt).trans (hdonor X).2.2.1)
      ((Nat.succ_le_of_lt v.isLt).trans (hdonor X).2.2.2)
  let encode : Bad × Fin V → Table r c × ((I × J) × Fin t) := fun p =>
    (next p.1 p.2, donor p.1, ⟨p.1.val.val a s, p.1.property⟩)
  have hinj : Function.Injective encode := by
    rintro ⟨X, v⟩ ⟨Y, w⟩ heq
    have hout : next X v = next Y w := congrArg Prod.fst heq
    have hd : donor X = donor Y := congrArg (fun z => z.2.1) heq
    have hh : X.val.val a s = Y.val.val a s :=
      congrArg (fun z => z.2.2.val) heq
    have hmarked := congrArg (fun Z : Table r c => Z.val a s) hout
    have hv : v = w := by
      apply Fin.ext
      dsimp [next] at hmarked
      simp only [fourCycle_marked] at hmarked
      omega
    have hXY : X.val = Y.val := by
      apply Subtype.ext
      funext i j
      have h := congrArg (fun Z : Table r c => (Z.val i j : ℤ)) hout
      dsimp [next] at h
      simp only [fourCycle_cast, fourCycleInt] at h
      rw [← hd, ← hv] at h
      exact Int.natCast_inj.mp (add_right_cancel h)
    exact Prod.ext (Subtype.ext hXY) hv
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    Fintype.card_le_of_injective encode hinj

omit [Fintype I] [DecidableEq I] in
private theorem donor_from_line (x : J → ℕ) (s : J) (d V : ℕ)
    (hsize : Fintype.card J ≤ d) (hV : 0 < V)
    (hmass : x s + d * V ≤ ∑ j, x j) :
    ∃ t, s ≠ t ∧ V ≤ x t := by
  by_contra hn
  have hlt (j : J) : (if j = s then 0 else x j) < V := by
    by_cases hj : j = s
    · simpa [hj] using hV
    · simp only [hj, ite_false]
      by_contra h
      exact hn ⟨j, Ne.symm hj, by omega⟩
  have hsum : (∑ j, if j = s then 0 else x j) < Fintype.card J * V := by
    have h := sum_lt_sum_of_nonempty (s := (univ : Finset J))
      ⟨s, mem_univ s⟩ (fun j _ => hlt j)
    simpa using h
  have hdecomp : (∑ j, if j = s then 0 else x j) + x s = ∑ j, x j := by
    calc
      _ = (∑ j, if j = s then 0 else x j) + (∑ j, if j = s then x s else 0) := by
        simp
      _ = ∑ j, ((if j = s then 0 else x j) + (if j = s then x s else 0)) :=
        sum_add_distrib.symm
      _ = ∑ j, x j := by
        apply sum_congr rfl
        intro j _
        by_cases hj : j = s <;> simp [hj]
  have hmul : Fintype.card J * V ≤ d * V := Nat.mul_le_mul_right V hsize
  omega

/-- Margin lower bounds supply the donors for each small marked entry.
`d * V + t ≤ a₀` is the discrete form of the manuscript's choice
`V = floor (a₀/(2d))` with `2t ≤ a₀`. -/
theorem small_entry_count {r : I → ℕ} {c : J → ℕ}
    (a : I) (s : J) (a₀ d t V : ℕ)
    (hrows : Fintype.card I ≤ d) (hcols : Fintype.card J ≤ d)
    (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s)
    (hV : 0 < V) (hscale : d * V + t ≤ a₀) :
    Fintype.card {X : Table r c // X.val a s < t} * V ≤
      Fintype.card (Table r c) * (Fintype.card I * Fintype.card J * t) := by
  apply small_entry_count_of_donors
  intro X hX
  obtain ⟨t', ht', hXt'⟩ := donor_from_line (X.val a) s d V hcols hV (by
    rw [X.property.1 a]
    omega)
  obtain ⟨b, hb, hXb⟩ := donor_from_line (fun i => X.val i s) a d V hrows hV (by
    rw [X.property.2 s]
    omega)
  exact ⟨(b, t'), hb, ht', hXt', hXb⟩

/-- The complete small-entry estimate of paper 200-01, expressed as the
uniform finite counting probability. It also covers zero rows or columns
away from the marked cell. -/
theorem small_entry_probability {r : I → ℕ} {c : J → ℕ}
    (htotal : ∑ i, r i = ∑ j, c j)
    (a : I) (s : J) (a₀ d t : ℕ) (hd : 0 < d)
    (hrows : Fintype.card I ≤ d) (hcols : Fintype.card J ≤ d)
    (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s)
    (ha₀ : 4 * d ≤ a₀) (ht : 2 * t ≤ a₀) :
    (Fintype.card {X : Table r c // X.val a s < t} : ℝ) /
        Fintype.card (Table r c) ≤ 4 * t * (d : ℝ) ^ 3 / a₀ := by
  classical
  let V := a₀ / (2 * d)
  have hV : 0 < V := Nat.div_pos (by omega) (by omega)
  have hfloor := Nat.mul_div_le a₀ (2 * d)
  change 2 * d * V ≤ a₀ at hfloor
  have hscale : d * V + t ≤ a₀ := by nlinarith [hfloor, ht]
  have hcount := small_entry_count a s a₀ d t V hrows hcols hrow hcol hV hscale
  have hmod := Nat.mod_lt a₀ (show 0 < 2 * d by omega)
  have hdiv := Nat.mod_add_div a₀ (2 * d)
  change a₀ % (2 * d) + 2 * d * V = a₀ at hdiv
  have hhalf : a₀ ≤ 4 * d * V := by nlinarith
  have hcard : 0 < Fintype.card (Table r c) :=
    Fintype.card_pos_iff.mpr (table_nonempty r c htotal)
  have hcardR : (0 : ℝ) < Fintype.card (Table r c) := by exact_mod_cast hcard
  have haR : (0 : ℝ) < a₀ := by exact_mod_cast (show 0 < a₀ by omega)
  have hfR : (a₀ : ℝ) ≤ 4 * d * V := by exact_mod_cast hhalf
  have hcR : (Fintype.card {X : Table r c // X.val a s < t} : ℝ) * V ≤
      Fintype.card (Table r c) * (Fintype.card I * Fintype.card J * (t : ℝ)) := by
    exact_mod_cast hcount
  have hsR : (Fintype.card I : ℝ) * Fintype.card J ≤ (d : ℝ) ^ 2 := by
    have h := Nat.mul_le_mul hrows hcols
    exact_mod_cast (show Fintype.card I * Fintype.card J ≤ d ^ 2 by
      simpa only [pow_two] using h)
  apply (div_le_div_iff₀ hcardR haR).mpr
  calc
    (Fintype.card {X : Table r c // X.val a s < t} : ℝ) * a₀ ≤
        Fintype.card {X : Table r c // X.val a s < t} * (4 * d * V) :=
      mul_le_mul_of_nonneg_left hfR (Nat.cast_nonneg _)
    _ = (4 * d) * (Fintype.card {X : Table r c // X.val a s < t} * (V : ℝ)) := by ring
    _ ≤ (4 * d) * (Fintype.card (Table r c) *
        (Fintype.card I * Fintype.card J * (t : ℝ))) :=
      mul_le_mul_of_nonneg_left hcR (by positivity)
    _ ≤ (4 * d) * (Fintype.card (Table r c) * ((d : ℝ) ^ 2 * t)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right hsR (Nat.cast_nonneg _)
    _ = (4 * t * (d : ℝ) ^ 3) * Fintype.card (Table r c) := by ring

end ContingencyTables

end OAI
