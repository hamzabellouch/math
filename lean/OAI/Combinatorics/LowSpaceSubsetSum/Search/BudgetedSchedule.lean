import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPreparedBucket
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedResidueLoop
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSchedule

namespace OAI

/-! # The concrete shared-budget residue schedule -/

namespace LowSpaceSubsetSum.BudgetedSchedule

variable {n g : ℕ}

def run (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (blocks : List (StoredSeparatorCheck.Block n g)) (target : ℤ) (budget : ℕ) :=
  BudgetedResidueLoop.run
    (fun z b => BudgetedPreparedBucket.run (D.bucket z) F F hF hF B blocks target b)
    0 D.q budget

theorem reference_eq (D : RepresentationScheduleData n g) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin g))) (z remaining : ℕ) :
    BudgetedResidueLoop.reference (fun z => (D.bucket z).run B families) z remaining =
      D.scanBuckets B families z remaining := by
  induction remaining generalizing z with
  | zero => rfl
  | succ remaining ih =>
    simp only [BudgetedResidueLoop.reference, RepresentationScheduleData.scanBuckets, ih]

theorem value (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (rows : Fin 4 → Vector (Fin n) g)
    (hrows : ∀ i j, (rows i)[j] = D.coordinates.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (target : ℤ) (htarget : target = D.target) (budget : ℕ) (v : Bool) (left : ℕ)
    (h : (run D F hF B (PreparedSeparatorContext.prepare rows families hsize).1
      target budget).1 = some (v, left)) :
    v = D.run B (fun i => (families i).map SeparatorStoredMasks.decode) := by
  subst target
  have hv := BudgetedResidueLoop.value
    (fun z b => BudgetedPreparedBucket.run (D.bucket z) F F hF hF B
      (PreparedSeparatorContext.prepare rows families hsize).1 D.target b)
    (fun z => (D.bucket z).run B (fun i => (families i).map SeparatorStoredMasks.decode))
    (fun z b v left he => (BudgetedPreparedBucket.value (D.bucket z) F F hF hF rfl B
      rows hrows families hsize b v left he).1) 0 D.q budget 0 v left h
  exact hv.trans (reference_eq D B _ 0 D.q)

noncomputable def allowance (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin g))) : ℕ :=
  BudgetedResidueLoop.allowance
    (fun z => BudgetedPreparedBucket.allowance (D.bucket z) F F hF hF B families) 0 D.q

theorem complete (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (hn : 10000 ≤ n) (hg : g ≤ n)
    (rows : Fin 4 → Vector (Fin n) g)
    (hrows : ∀ i j, (rows i)[j] = D.coordinates.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (target : ℤ) (htarget : target = D.target) (budget : ℕ)
    (hb : allowance D F hF B (fun i => (families i).map SeparatorStoredMasks.decode) ≤ budget) :
    ∃ v left, (run D F hF B (PreparedSeparatorContext.prepare rows families hsize).1
      target budget).1 = some (v, left) := by
  subst target
  exact BudgetedResidueLoop.complete _ _
    (fun z b hb => BudgetedPreparedBucket.complete (D.bucket z) F F hF hF B hn hg
      rows hrows families hsize b hb)
    (fun z b v left he => BudgetedPreparedBucket.remaining (D.bucket z) F F hF hF B hn hg
      rows hrows families hsize b v left he) 0 D.q budget 0 hb

end LowSpaceSubsetSum.BudgetedSchedule

end OAI
