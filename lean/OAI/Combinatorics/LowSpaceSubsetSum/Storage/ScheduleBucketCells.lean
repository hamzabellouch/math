import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ConcretePrefixCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PreparedCheckerCells
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.LiveSequence
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPreparedBucket

namespace OAI

/-! # One residue bucket with a retained left dictionary and reused right workspace -/

namespace LowSpaceSubsetSum.ScheduleBucketCells

open BudgetedSeparatorCells
variable {n g : ℕ}

def afterLeft (D : RepresentationScheduleData n g) (z : ℕ) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (blocks : List (StoredSeparatorCheck.Block n g))
    (target : ℤ) (left : StoredEntry.Dictionary D.input D.capacity) (budget : ℕ) : Execution Bool :=
  if left.val.keys.overflow || left.val.records.isEmpty then
    (BudgetedSeparatorFlow.pure false budget, 0)
  else
    ConcretePrefixCells.run (D.parentData 1 z) F hF B
      (fun right b => BudgetedCheckerCells.arrays (PreparedCheckerCells.scratch n g)
        (2 ^ n) target blocks left.val.records right b)
      D.topOrder StoredRestriction.empty budget

def run (D : RepresentationScheduleData n g) (z : ℕ) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (blocks : List (StoredSeparatorCheck.Block n g))
    (target : ℤ) (budget : ℕ) : Execution Bool :=
  LiveSequence.run (fun _ : Unit => 0)
    (BudgetedSeparatorCall.run 8 (fun _ => ((), 7)) budget, 8) fun _ rest =>
    LiveSequence.run ParentLiveState.dictionary
      (BudgetedPrefixCells.collect (D.parentData 0 z) F hF B StoredRestriction.empty rest)
      (afterLeft D z F hF B blocks target)

theorem afterLeft_value (D : RepresentationScheduleData n g) (z : ℕ) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (blocks : List (StoredSeparatorCheck.Block n g))
    (target : ℤ) (left : StoredEntry.Dictionary D.input D.capacity) (budget : ℕ) :
    (afterLeft D z F hF B blocks target left budget).1 =
      if left.val.keys.overflow || left.val.records.isEmpty then
        BudgetedSeparatorFlow.pure false budget
      else BudgetedConcretePrefix.run (D.parentData 1 z) F hF B
        (BudgetedSeparatorArrays.execute (2 ^ n) target blocks left.val.records)
        D.topOrder StoredRestriction.empty budget := by
  unfold afterLeft
  split
  · rfl
  · have hv := ConcretePrefixCells.value (D.parentData 1 z) F hF B
      (fun right b => BudgetedCheckerCells.arrays (PreparedCheckerCells.scratch n g)
        (2 ^ n) target blocks left.val.records right b)
      D.topOrder StoredRestriction.empty budget
    simpa only [BudgetedCheckerCells.arrays_value] using hv

theorem value (D : RepresentationScheduleData n g) (z : ℕ) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (blocks : List (StoredSeparatorCheck.Block n g))
    (target : ℤ) (budget : ℕ) :
    (run D z F hF B blocks target budget).1 =
      BudgetedPreparedBucket.run (D.bucket z) F F hF hF B blocks target budget := by
  have inner (rest : ℕ) := congrArg₂ BudgetedSeparatorFlow.bind
    (BudgetedPrefixCells.collect_value (D.parentData 0 z) F hF B StoredRestriction.empty rest)
    (funext (fun left => funext (fun available =>
      afterLeft_value D z F hF B blocks target left available)))
  simp only [run, LiveSequence.value, BudgetedPreparedBucket.run, BudgetedBucket.run,
    RepresentationScheduleData.bucket]
  congr 1
  funext a b
  exact (LiveSequence.value ParentLiveState.dictionary
    (BudgetedPrefixCells.collect (D.parentData 0 z) F hF B StoredRestriction.empty b)
    (afterLeft D z F hF B blocks target)).trans (inner b)

/-- The complete live left dictionary has at most one rejected extra record. -/
theorem records_size (I : Instance n) (C : ℕ) (d : StoredEntry.Dictionary I C) :
    d.val.records.size ≤ C + 1 := (RecordedDictionary.storage d.property).1

def reserve (D : RepresentationScheduleData n g) : ℕ :=
  BudgetedPrefixCells.frame n * (D.topOrder.length + 1) +
    inputScale D.input ^ 14 * (D.capacity + 1) +
    inputScale D.input ^ 2 * (D.capacity + 1) +
    inputScale D.input ^ 5 * (2 * (D.capacity + 1) + 1)

theorem afterLeft_cells (D : RepresentationScheduleData n g) (z : ℕ) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (blocks : List (StoredSeparatorCheck.Block n g))
    (target : ℤ) (left : StoredEntry.Dictionary D.input D.capacity) (budget : ℕ)
    (hn : 10000 ≤ n) (hg : g ≤ n)
    (rows : Fin 4 → Vector (Fin n) g) (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (hblocks : blocks = (PreparedSeparatorContext.prepare rows families hsize).1)
    (hraw : ∀ side i, (D.leaves side i).occurrences.card ≤ D.capacity)
    (hC : D.capacity ≤ 2 ^ n) (hB : B ≤ D.capacity) :
    (afterLeft D z F hF B blocks target left budget).2 ≤ reserve D := by
  unfold afterLeft
  split
  · exact Nat.zero_le _
  · apply ConcretePrefixCells.cells (D.parentData 1 z) F hF B _
      (inputScale D.input ^ 5 * (2 * (D.capacity + 1) + 1)) _ D.topOrder
      StoredRestriction.empty budget hn _ _ hC hB
    · intro right b
      have hl := records_size D.input D.capacity left
      have hr := records_size D.input D.capacity right
      rw [hblocks]
      exact PreparedCheckerCells.arrays_cells D.input hn hg rows families hsize (2 ^ n)
        target left.val.records right.val.records b (2 * (D.capacity + 1)) (by omega)
    · intro j
      exact hraw 1 ⟨2 * j.val, by omega⟩
    · intro j
      exact hraw 1 ⟨2 * j.val + 1, by omega⟩

theorem cells_explicit (D : RepresentationScheduleData n g) (z : ℕ) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (blocks : List (StoredSeparatorCheck.Block n g))
    (target : ℤ) (budget : ℕ) (hn : 10000 ≤ n) (hg : g ≤ n)
    (rows : Fin 4 → Vector (Fin n) g) (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (hblocks : blocks = (PreparedSeparatorContext.prepare rows families hsize).1)
    (hraw : ∀ side i, (D.leaves side i).occurrences.card ≤ D.capacity)
    (hC : D.capacity ≤ 2 ^ n) (hB : B ≤ D.capacity) :
    (run D z F hF B blocks target budget).2 ≤
      8 + inputScale D.input ^ 14 * (D.capacity + 1) +
        inputScale D.input ^ 2 * (D.capacity + 1) + reserve D := by
  have hinner (b : ℕ) := LiveSequence.cells ParentLiveState.dictionary
    (BudgetedPrefixCells.collect (D.parentData 0 z) F hF B StoredRestriction.empty b)
    (afterLeft D z F hF B blocks target)
    (inputScale D.input ^ 14 * (D.capacity + 1))
    (inputScale D.input ^ 2 * (D.capacity + 1)) (reserve D)
    (BudgetedPrefixCells.collect_cells (D.parentData 0 z) F hF B StoredRestriction.empty b hn
      (fun j => hraw 0 ⟨2*j.val, by omega⟩)
      (fun j => hraw 0 ⟨2*j.val+1, by omega⟩) hC hB)
    (fun d _ _ => ConcretePrefixCells.dictionary_bound D.input D.capacity hn d)
    (fun d b _ => afterLeft_cells D z F hF B blocks target d b hn hg
      rows families hsize hblocks hraw hC hB)
  have hout := LiveSequence.cells (fun _ : Unit => 0)
    (BudgetedSeparatorCall.run 8 (fun _ => ((), 7)) budget, 8)
    (fun _ b => LiveSequence.run ParentLiveState.dictionary
      (BudgetedPrefixCells.collect (D.parentData 0 z) F hF B StoredRestriction.empty b)
      (afterLeft D z F hF B blocks target)) 8 0
    (inputScale D.input ^ 14 * (D.capacity + 1) +
      inputScale D.input ^ 2 * (D.capacity + 1) + reserve D)
    le_rfl (fun _ _ _ => le_rfl) (by intro _ b _; exact (hinner b).trans (max_le (by omega) (by omega)))
  exact hout.trans (max_le (by omega) (by omega))

theorem cells (D : RepresentationScheduleData n g) (z : ℕ) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (blocks : List (StoredSeparatorCheck.Block n g))
    (target : ℤ) (budget : ℕ) (hn : 10000 ≤ n) (hg : g ≤ n)
    (rows : Fin 4 → Vector (Fin n) g) (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (hblocks : blocks = (PreparedSeparatorContext.prepare rows families hsize).1)
    (hraw : ∀ side i, (D.leaves side i).occurrences.card ≤ D.capacity)
    (hC : D.capacity ≤ 2 ^ n) (hB : B ≤ D.capacity) (ho : D.topOrder.length ≤ n) :
    (run D z F hF B blocks target budget).2 ≤
      30 * inputScale D.input ^ 14 * (D.capacity + 1) := by
  have ht := cells_explicit D z F hF B blocks target budget hn hg rows families hsize
    hblocks hraw hC hB
  let u := inputScale D.input
  let C := D.capacity
  let L := u ^ 14 * (C + 1)
  have hu : n+1 ≤ u := by dsimp [u, inputScale]; omega
  have hu0 : 10000 ≤ u := by omega
  have hpow (k : ℕ) (hk : k ≤ 14) : u ^ k ≤ u ^ 14 := pow_le_pow_right' (by omega) hk
  have h2 : u ^ 2 * (C+1) ≤ L := Nat.mul_le_mul_right _ (hpow 2 (by decide))
  have h3 : u ^ 3 ≤ L := (hpow 3 (by decide)).trans (Nat.le_mul_of_pos_right _ (by omega))
  have h5 := Nat.mul_le_mul_right (C+1) (hpow 5 (by decide))
  have hf : BudgetedPrefixCells.frame n * (D.topOrder.length+1) ≤ 20 * u ^ 3 := by
    have ha := Nat.pow_le_pow_left hu 2
    have hb : D.topOrder.length+1 ≤ u := by omega
    have hm := Nat.mul_le_mul ha hb
    unfold BudgetedPrefixCells.frame
    nlinarith only [hm]
  have hc : u ^ 5 * (2*(C+1)+1) ≤ 3*L := by
    have hm := Nat.mul_le_mul_left (u ^ 5) (show 2*(C+1)+1 ≤ 3*(C+1) by omega)
    change _ ≤ 3*(u^14*(C+1))
    nlinarith only [hm, h5]
  have h8 : 8 ≤ L := by
    have hu14 : u ≤ u ^ 14 := by simpa only [pow_one] using hpow 1 (by decide)
    have hm : u ^ 14 ≤ L := Nat.le_mul_of_pos_right _ (by omega)
    omega
  change _ ≤ 30 * (u ^ 14) * (C+1)
  change _ ≤ 8 + L + u ^ 2*(C+1) + (BudgetedPrefixCells.frame n *
    (D.topOrder.length+1)+L+u^2*(C+1)+u^5*(2*(C+1)+1)) at ht
  dsimp only [L] at ht h2 h3 hc h8
  nlinarith only [ht, h2, h3, hf, hc, h8]

end LowSpaceSubsetSum.ScheduleBucketCells

end OAI
