import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BudgetedCheckerCells
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedPreparedSeparator

namespace OAI

/-! # Four prepared blocks have polynomial live-buffer overhead -/

namespace LowSpaceSubsetSum.PreparedCheckerCells

open StoredSeparatorCheck

variable {n g : ℕ}

def scratch (n g : ℕ) : ℕ := (4 * (n + 1) + 16) * (g + 1) ^ 2 + 40

theorem scratch_bound (I : Instance n) (hg : g ≤ n) :
    scratch n g ≤ 60 * inputScale I ^ 3 := by
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hg' : g + 1 ≤ inputScale I := by omega
  have hc : 4 * (n + 1) + 16 ≤ 20 * inputScale I := by omega
  have hm := Nat.mul_le_mul hc (Nat.pow_le_pow_left hg' 2)
  have hp : 1 ≤ inputScale I ^ 3 := by
    simpa using Nat.pow_le_pow_left (show 1 ≤ inputScale I by omega) 3
  unfold scratch
  nlinarith only [hm, hp]

theorem query_left_cells (b : Block n g) (x : StoredEntry n) (lo hi : ℕ) :
    (StoredQueryCells.query b.row x b.leftStore b.leftSize b.steps lo hi).2 ≤ scratch n g :=
  StoredQueryCells.query_cells _ _ _ _ _ _ _

theorem query_right_cells (b : Block n g) (x : StoredEntry n) (lo hi : ℕ) :
    (StoredQueryCells.query b.row x b.rightStore b.rightSize b.steps lo hi).2 ≤ scratch n g :=
  StoredQueryCells.query_cells _ _ _ _ _ _ _

theorem query_left_value (b : Block n g) (x : StoredEntry n) (lo hi : ℕ) :
    (StoredQueryCells.query b.row x b.leftStore b.leftSize b.steps lo hi).1 = b.leftQuery x lo hi :=
  StoredQueryCells.query_value _ _ _ _ _ _ _

theorem query_right_value (b : Block n g) (x : StoredEntry n) (lo hi : ℕ) :
    (StoredQueryCells.query b.row x b.rightStore b.rightSize b.steps lo hi).1 = b.rightQuery x lo hi :=
  StoredQueryCells.query_value _ _ _ _ _ _ _

theorem prepared_depths (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) (hg : g ≤ n) :
    ∀ b ∈ (PreparedSeparatorContext.prepare rows families hsize).1, b.depth ≤ n + 4 := by
  intro b hb
  rw [PreparedSeparatorContext.prepare_value, prepareFour_value] at hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  change PreparedSeparatorContext.depths families i ≤ n + 4
  rw [PreparedSeparatorContext.depths_value families hsize i]
  exact (Nat.clog_le_of_le_pow
    (PreparedSeparatorWork.family_search_bound (families i) (hsize i)).le).trans (by omega)

private theorem numeric (I : Instance n) (hn : 10000 ≤ n) (C H : ℕ)
    (hH : H ≤ 60 * inputScale I ^ 3) :
    4 * (C + 1) + (8 + 72 * (n + 1) * (C + 1) +
      4 * (8 + (n + 4 + 1) * (8 * (C + 1) + H))) ≤
      inputScale I ^ 5 * (C + 1) := by
  let u := inputScale I
  have hu : n + 1 ≤ u := by unfold u inputScale; omega
  have hlarge : 1000 ≤ u := by omega
  have hn5 : n + 4 + 1 ≤ 2 * u := by omega
  have hm := Nat.mul_le_mul hn5 (Nat.add_le_add_left hH (8 * (C + 1)))
  have hsmall : u ≤ u ^ 4 := Nat.le_self_pow (by decide) u
  have hone : 1 ≤ u ^ 4 := by
    simpa using Nat.pow_le_pow_left (show 1 ≤ u by omega) 4
  have hv := Nat.mul_le_mul_right (C + 1) hsmall
  have hC := Nat.mul_le_mul_right (C + 1) hone
  have hp := Nat.mul_le_mul_left (u ^ 4) (show 1 ≤ C + 1 by omega)
  have hbound : 4 * (C + 1) + (8 + 72 * (n + 1) * (C + 1) +
      4 * (8 + (n + 4 + 1) * (8 * (C + 1) + H))) ≤ 1000 * u ^ 4 * (C + 1) := by
    have hlin := Nat.mul_le_mul_right (C + 1) hu
    change H ≤ 60 * u ^ 3 at hH
    change (n + 4 + 1) * (8 * (C + 1) + H) ≤
      2 * u * (8 * (C + 1) + 60 * u ^ 3) at hm
    nlinarith only [hm, hlin, hv, hC, hp]
  exact hbound.trans (by
    change 1000 * u ^ 4 * (C + 1) ≤ u ^ 5 * (C + 1)
    have h := Nat.mul_le_mul_right (u ^ 4 * (C + 1)) hlarge
    nlinarith only [h])

theorem arrays_cells (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (capacity : ℕ) (target : ℤ) (left right : Array (StoredEntry n)) (budget C : ℕ)
    (hC : left.size + right.size ≤ C) :
    (BudgetedCheckerCells.arrays (scratch n g) capacity target
      (PreparedSeparatorContext.prepare rows families hsize).1 left right budget).2 ≤
      inputScale I ^ 5 * (C + 1) := by
  have ha := BudgetedCheckerCells.arrays_cells (scratch n g) capacity target
    (PreparedSeparatorContext.prepare rows families hsize).1 left right budget C hC
  have hb := BudgetedCheckerCells.bound_le (scratch n g) C (n + 4)
    (PreparedSeparatorContext.prepare rows families hsize).1
    (prepared_depths rows families hsize hg)
  have hlen : (PreparedSeparatorContext.prepare rows families hsize).1.length = 4 := by
    rw [PreparedSeparatorContext.prepare_value]
    exact prepareFour_length _ _ _ _ _ _
  rw [hlen] at hb
  exact ha.trans ((Nat.add_le_add_left hb _).trans (numeric I hn C _ (scratch_bound I hg)))

private theorem list_payload (xs : List (StoredEntry n)) :
    (xs.map StoredEntry.cells).sum ≤ (n + 2) * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := x.cells_le
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- Original entry payloads and their array slots remain shared throughout
all filtering, sorting and recursion. -/
def retained (left right : Array (StoredEntry n)) : ℕ :=
  (left.toList.map StoredEntry.cells).sum + (right.toList.map StoredEntry.cells).sum +
    left.size + right.size + 2

theorem retained_le (left right : Array (StoredEntry n)) :
    retained left right ≤ (n + 3) * (left.size + right.size) + 2 := by
  have hl := list_payload left.toList
  have hr := list_payload right.toList
  simp only [Array.length_toList] at hl hr
  unfold retained
  nlinarith only [hl, hr]

theorem arrays_with_payload (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (capacity : ℕ) (target : ℤ) (left right : Array (StoredEntry n)) (budget C : ℕ)
    (hC : left.size + right.size ≤ C) :
    retained left right +
      (BudgetedCheckerCells.arrays (scratch n g) capacity target
        (PreparedSeparatorContext.prepare rows families hsize).1 left right budget).2 ≤
      inputScale I ^ 6 * (C + 1) := by
  have he := arrays_cells I hn hg rows families hsize capacity target left right budget C hC
  have hr := (retained_le left right).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left (n + 3) hC) 2)
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hu2 : n + 3 ≤ inputScale I ^ 2 := by nlinarith only [hu, hn]
  have hp : 2 ≤ inputScale I ^ 2 := by nlinarith only [hu, hn]
  have hret : retained left right ≤ inputScale I ^ 2 * (C + 1) := by
    have hm := Nat.mul_le_mul_right C hu2
    nlinarith only [hr, hm, hp]
  have hpow : inputScale I ^ 2 ≤ inputScale I ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hcoef : inputScale I ^ 2 + inputScale I ^ 5 ≤ inputScale I ^ 6 := by
    have hmul := Nat.mul_le_mul_right (inputScale I ^ 5)
      (show 2 ≤ inputScale I by omega)
    nlinarith only [hpow, hmul]
  have htotal := Nat.mul_le_mul_right (C + 1) hcoef
  nlinarith only [he, hret, htotal]

end LowSpaceSubsetSum.PreparedCheckerCells

end OAI
