import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ScheduleCells
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPreparedSchedule

namespace OAI

/-! # Shared incidence preparation and the full stopped residue schedule -/

namespace LowSpaceSubsetSum.PreparedScheduleCells

open BudgetedSeparatorCells
variable {n g : ℕ}

def keep (blocks : List (StoredSeparatorCheck.Block n g)) : ℕ :=
  (blocks.map PreparedIncidenceCells.payload).sum + blocks.length + 4

def run (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (rows : Fin 4 → Vector (Fin n) g) (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) (budget : ℕ) : Execution Bool :=
  LiveSequence.run keep (BudgetedIncidencePreparation.execute rows families hsize budget)
    (fun blocks left => ScheduleCells.run D F hF B blocks D.target left)

theorem value (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (rows : Fin 4 → Vector (Fin n) g) (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) (budget : ℕ) :
    (run D F hF B rows families hsize budget).1 =
      BudgetedPreparedSchedule.run D F hF B rows families hsize budget := by
  simp only [run, LiveSequence.value, ScheduleCells.value, BudgetedPreparedSchedule.run]

theorem keep_bound (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    keep (PreparedSeparatorContext.prepare rows families hsize).1 ≤
      104 * 2 ^ (2 * g) + 4 * g + 40 := by
  have hp (i : Fin 4) := PreparedIncidenceCells.prepareBlock_payload (rows i) (families i)
    (PreparedSeparatorContext.depths families i) (g+4)
    (PreparedSeparatorContext.depths_value families hsize i)
    (PreparedSeparatorWork.family_search_bound (families i) (hsize i)) (hsize i)
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  rw [← PreparedIncidenceCells.prepare_value rows families hsize]
  simp only [keep, PreparedIncidenceCells.prepare, PreparedIncidenceCells.prepareFour,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
  dsimp only [PreparedSeparatorContext.depths] at h0 h1 h2 h3
  omega

theorem keep_scale (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : ℕ) (hC : 2 ^ (2*g) ≤ C)
    (rows : Fin 4 → Vector (Fin n) g) (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    keep (PreparedSeparatorContext.prepare rows families hsize).1 ≤ inputScale I ^ 2 * (C+1) := by
  have hk := keep_bound rows families hsize
  have hC0 : 1 ≤ C := Nat.one_le_two_pow.trans hC
  have hu : n+1 ≤ inputScale I := by unfold inputScale; omega
  have hcoef : 104 + 4*g + 40 ≤ inputScale I ^ 2 := by nlinarith only [hu, hg, hn]
  have hm := Nat.mul_le_mul_right (C+1) hcoef
  have hp := Nat.mul_le_mul_left 104 hC
  have hlin := Nat.mul_le_mul_left (4*g+40) (show 1 ≤ C+1 by omega)
  nlinarith only [hk, hm, hp, hlin]

theorem cells (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (rows : Fin 4 → Vector (Fin n) g) (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) (budget : ℕ)
    (hn : 10000 ≤ n) (hg : g ≤ n)
    (hraw : ∀ side i, (D.leaves side i).occurrences.card ≤ D.capacity)
    (hC : D.capacity ≤ 2 ^ n) (hB : B ≤ D.capacity) (ho : D.topOrder.length ≤ n)
    (ht : 2 ^ (2*g) ≤ D.capacity) :
    (run D F hF B rows families hsize budget).2 ≤
      32 * inputScale D.input ^ 14 * (D.capacity+1) + 16 := by
  have hp := BudgetedIncidencePreparation.cells_with_inputs D.input hn hg D.capacity ht
    rows families hsize budget
  have hk := keep_scale D.input hn hg D.capacity ht rows families hsize
  have he := LiveSequence.cells keep (BudgetedIncidencePreparation.execute rows families hsize budget)
    (fun blocks left => ScheduleCells.run D F hF B blocks D.target left)
    (inputScale D.input ^ 3 * (D.capacity+1))
    (inputScale D.input ^ 2 * (D.capacity+1))
    (30 * inputScale D.input ^ 14 * (D.capacity+1)+16)
    (by omega)
    (by intro blocks left h; rw [(BudgetedIncidencePreparation.value rows families hsize budget blocks left h).1]; exact hk)
    (by
      intro blocks left h
      exact ScheduleCells.cells D F hF B blocks D.target left hn hg rows families hsize
        (BudgetedIncidencePreparation.value rows families hsize budget blocks left h).1
        hraw hC hB ho)
  have hu : 1 ≤ inputScale D.input := by unfold inputScale; omega
  have h3 := Nat.mul_le_mul_right (D.capacity+1)
    (pow_le_pow_right' hu (by decide : 3 ≤ 14))
  have h2 := Nat.mul_le_mul_right (D.capacity+1)
    (pow_le_pow_right' hu (by decide : 2 ≤ 14))
  apply he.trans
  simp only [Nat.mul_assoc]
  exact max_le (h3.trans (by omega)) (by omega)

end LowSpaceSubsetSum.PreparedScheduleCells

end OAI
