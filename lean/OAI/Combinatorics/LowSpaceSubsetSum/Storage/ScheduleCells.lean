import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ResidueLoopCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ScheduleBucketCells
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedSchedule

namespace OAI

/-! # One reused parent workspace across every residue -/

namespace LowSpaceSubsetSum.ScheduleCells

variable {n g : ℕ}

def run (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (blocks : List (StoredSeparatorCheck.Block n g))
    (target : ℤ) (budget : ℕ) :=
  ResidueLoopCells.run (fun z b => ScheduleBucketCells.run D z F hF B blocks target b)
    0 D.q budget

theorem value (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (blocks : List (StoredSeparatorCheck.Block n g))
    (target : ℤ) (budget : ℕ) :
    (run D F hF B blocks target budget).1 = BudgetedSchedule.run D F hF B blocks target budget := by
  rw [run, ResidueLoopCells.value]
  simp only [ScheduleBucketCells.value, BudgetedSchedule.run]

theorem cells (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (blocks : List (StoredSeparatorCheck.Block n g))
    (target : ℤ) (budget : ℕ) (hn : 10000 ≤ n) (hg : g ≤ n)
    (rows : Fin 4 → Vector (Fin n) g) (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (hblocks : blocks = (PreparedSeparatorContext.prepare rows families hsize).1)
    (hraw : ∀ side i, (D.leaves side i).occurrences.card ≤ D.capacity)
    (hC : D.capacity ≤ 2 ^ n) (hB : B ≤ D.capacity) (ho : D.topOrder.length ≤ n) :
    (run D F hF B blocks target budget).2 ≤
      30 * inputScale D.input ^ 14 * (D.capacity + 1) + 16 :=
  ResidueLoopCells.cells _ _
    (fun z b => ScheduleBucketCells.cells D z F hF B blocks target b hn hg rows families
      hsize hblocks hraw hC hB ho) 0 D.q budget

end LowSpaceSubsetSum.ScheduleCells

end OAI
