import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedReplay
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedParentJoin

namespace OAI

/-! # Interruptible concrete parent suffix reporting

Each iteration prepays its bounded-mask reader, modular key, validity and
dictionary work before any of those implementations is called.
-/

namespace LowSpaceSubsetSum.BudgetedParentReplay

variable {n : ℕ}

def run (I : Instance n) (F : IndexedMask n) (P t K : ℤ) (C : ℕ)
    (right : Array (LeafRecord n)) {d : ℕ} (x : CountedParentJoin.Child n)
    (fuel : ℕ) (s : CountedParentJoin.State I F P (.complementary t) right d)
    (a : StoredEntry.Dictionary I C) (budget : ℕ) :=
  BudgetedReplay.runAcc (inputScale I ^ 6)
    (fun s => (RepresentationKeys.read I F P (.complementary t) right s).1)
    (fun y => (RepresentationKeys.pairKey I F P (.complementary t) y).1) K
    (fun y a => (StoredEntry.report I C (CountedRepresentationEmit.emit I F) x y a).1)
    fuel s a 0 0 budget

def reference (I : Instance n) (F : IndexedMask n) (P t K : ℤ) (C : ℕ)
    (right : Array (LeafRecord n)) {d : ℕ} (x : CountedParentJoin.Child n)
    (fuel : ℕ) (s : CountedParentJoin.State I F P (.complementary t) right d)
    (a : StoredEntry.Dictionary I C) :=
  CountedReplay.run (RepresentationKeys.read I F P (.complementary t) right)
    (RepresentationKeys.pairKey I F P (.complementary t)) K
    (fun y a => StoredEntry.report I C (CountedRepresentationEmit.emit I F) x y a)
    fuel s a

def execute (I : Instance n) (F : IndexedMask n) (P t K : ℤ) (C : ℕ)
    (right : Array (LeafRecord n)) {d : ℕ} (x : CountedParentJoin.Child n)
    (fuel : ℕ) (s : CountedParentJoin.State I F P (.complementary t) right d)
    (a : StoredEntry.Dictionary I C) (budget : ℕ) :=
  BudgetedReplay.execute (inputScale I ^ 6)
    (RepresentationKeys.read I F P (.complementary t) right)
    (RepresentationKeys.pairKey I F P (.complementary t)) K
    (fun y a => StoredEntry.report I C (CountedRepresentationEmit.emit I F) x y a)
    fuel s a 0 0 budget

theorem execute_value (I : Instance n) (F : IndexedMask n) (P t K : ℤ) (C : ℕ)
    (right : Array (LeafRecord n)) {d : ℕ} (x : CountedParentJoin.Child n)
    (fuel : ℕ) (s : CountedParentJoin.State I F P (.complementary t) right d)
    (a : StoredEntry.Dictionary I C) (budget : ℕ) :
    (execute I F P t K C right x fuel s a budget).1 = run I F P t K C right x fuel s a budget :=
  BudgetedReplay.execute_value _ _ _ _ _ _ _ _ _ _ _

theorem completed_value (I : Instance n) (F : IndexedMask n) (P t K : ℤ) (C : ℕ)
    (right : Array (LeafRecord n)) {d : ℕ} (x : CountedParentJoin.Child n)
    (fuel : ℕ) (s : CountedParentJoin.State I F P (.complementary t) right d)
    (a : StoredEntry.Dictionary I C) (budget : ℕ)
    (out : TieReplay.Result (CountedParentJoin.State I F P (.complementary t) right d)
      (StoredEntry.Dictionary I C)) (left : ℕ)
    (h : run I F P t K C right x fuel s a budget = some (out, left)) :
    out = (reference I F P t K C right x fuel s a).1 ∧ left ≤ budget := by
  have hv := BudgetedReplay.runAcc_value _ _ _ _ _ fuel s a 0 0 budget out left h
  rw [reference, CountedReplay.run_value]
  exact hv

theorem complete (I : Instance n) (F : IndexedMask n) (P t K : ℤ) (C : ℕ)
    (right : Array (LeafRecord n)) {d : ℕ} (x : CountedParentJoin.Child n)
    (fuel : ℕ) (s : CountedParentJoin.State I F P (.complementary t) right d)
    (a : StoredEntry.Dictionary I C) (budget : ℕ)
    (hbudget : inputScale I ^ 6 *
      ((reference I F P t K C right x fuel s a).1.queries + 1) ≤ budget) :
    ∃ left, run I F P t K C right x fuel s a budget =
      some ((reference I F P t K C right x fuel s a).1, left) := by
  simp only [reference, CountedReplay.run_value] at hbudget ⊢
  exact BudgetedReplay.runAcc_complete _ _ _ _ _ fuel s a 0 0 budget
    (by simpa only [Nat.sub_zero, TieReplay.run] using hbudget)

private theorem iteration_charge {u : ℕ} (hu : 10000 ≤ u) :
    u ^ 5 + u ^ 3 + u ^ 4 + 8 ≤ u ^ 6 := by
  have h3 : u ^ 3 ≤ u ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : u ^ 4 ≤ u ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : 1 ≤ u ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hm : 11 * u ^ 5 ≤ u ^ 6 := by
    calc
      _ ≤ u * u ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' u 5).symm
  omega

theorem completed_work (I : Instance n) (F : IndexedMask n) (P t K : ℤ) (C : ℕ)
    (right : Array (LeafRecord n)) {d : ℕ} (x : CountedParentJoin.Child n)
    (fuel : ℕ) (s : CountedParentJoin.State I F P (.complementary t) right d)
    (a : StoredEntry.Dictionary I C) (budget : ℕ)
    (out : TieReplay.Result (CountedParentJoin.State I F P (.complementary t) right d)
      (StoredEntry.Dictionary I C)) (left : ℕ)
    (hn : 10000 ≤ n) (hd : d ≤ n)
    (h : run I F P t K C right x fuel s a budget = some (out, left)) :
    (reference I F P t K C right x fuel s a).2 ≤ budget - left := by
  have hnu : n ≤ inputScale I := by unfold inputScale; omega
  exact BudgetedReplay.runAcc_work
    (RepresentationKeys.read I F P (.complementary t) right)
    (RepresentationKeys.pairKey I F P (.complementary t)) K
    (fun y a => StoredEntry.report I C (CountedRepresentationEmit.emit I F) x y a)
    (inputScale I ^ 5) (inputScale I ^ 3) (inputScale I ^ 4) (inputScale I ^ 6)
    (fun s => RepresentationKeys.read_scale I F P (.complementary t) right s hd hn)
    (fun y => RepresentationKeys.pairKey_scale I F P (.complementary t) y hn)
    (fun y a => CountedParentJoin.report_work I F C x y a hn)
    (iteration_charge (hn.trans hnu)) fuel s a 0 0 budget out left h

/-- The concrete suffix execution respects its prepaid budget even when it
times out, with one additional operation for the final failed budget test. -/
theorem execute_work (I : Instance n) (F : IndexedMask n) (P t K : ℤ) (C : ℕ)
    (right : Array (LeafRecord n)) {d : ℕ} (x : CountedParentJoin.Child n)
    (fuel : ℕ) (s : CountedParentJoin.State I F P (.complementary t) right d)
    (a : StoredEntry.Dictionary I C) (budget : ℕ) (hn : 10000 ≤ n) (hd : d ≤ n) :
    (execute I F P t K C right x fuel s a budget).2 ≤ budget + 1 := by
  have hnu : n ≤ inputScale I := by unfold inputScale; omega
  exact BudgetedReplay.execute_work
    (RepresentationKeys.read I F P (.complementary t) right)
    (RepresentationKeys.pairKey I F P (.complementary t)) K
    (fun y a => StoredEntry.report I C (CountedRepresentationEmit.emit I F) x y a)
    (inputScale I ^ 5) (inputScale I ^ 3) (inputScale I ^ 4) (inputScale I ^ 6)
    (fun s => RepresentationKeys.read_scale I F P (.complementary t) right s hd hn)
    (fun y => RepresentationKeys.pairKey_scale I F P (.complementary t) y hn)
    (fun y a => CountedParentJoin.report_work I F C x y a hn)
    (iteration_charge (hn.trans hnu)) fuel s a 0 0 budget

end LowSpaceSubsetSum.BudgetedParentReplay

end OAI
