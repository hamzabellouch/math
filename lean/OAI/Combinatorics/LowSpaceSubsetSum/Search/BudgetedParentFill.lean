import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedFill
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedParentJoin

namespace OAI

/-! # Prepaid buffer filling with the actual bounded-mask reader and key -/

namespace LowSpaceSubsetSum.BudgetedParentFill

variable {n : ℕ}

def execute (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) (right : Array (LeafRecord n)) {d : ℕ}
    (K : ℤ) (fuel : ℕ) (s : CountedParentJoin.State I F P mode right d)
    (buf : Array (CountedParentJoin.Child n)) (q budget : ℕ) :=
  BudgetedFill.execute (inputScale I ^ 6) (RepresentationKeys.read I F P mode right)
    (RepresentationKeys.pairKey I F P mode) CountedParentJoin.cells K fuel s buf q budget

theorem completed_value (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) (right : Array (LeafRecord n)) {d : ℕ}
    (K : ℤ) (fuel : ℕ) (s : CountedParentJoin.State I F P mode right d)
    (buf : Array (CountedParentJoin.Child n)) (q budget : ℕ)
    (out : TieBuffer.Result (CountedParentJoin.Child n)
      (CountedParentJoin.State I F P mode right d)) (left : ℕ)
    (h : (execute I F P mode right K fuel s buf q budget).1 = some (out, left)) :
    out = (CountedFill.fillAcc (RepresentationKeys.read I F P mode right)
      (RepresentationKeys.pairKey I F P mode) CountedParentJoin.cells K fuel s buf q).1 ∧
        left ≤ budget :=
  BudgetedFill.execute_value _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem iteration_charge {n u : ℕ} (hnu : n ≤ u) (hu : 10000 ≤ u) :
    u ^ 5 + u ^ 3 + (6 * n + 4) + 8 ≤ u ^ 6 := by
  have hu1 : 1 ≤ u := by omega
  have h15 : u ≤ u ^ 5 := by simpa using Nat.pow_le_pow_right hu1 (by decide : 1 ≤ 5)
  have h35 : u ^ 3 ≤ u ^ 5 := Nat.pow_le_pow_right hu1 (by decide)
  have hc : 12 ≤ 12 * u ^ 5 := Nat.le_mul_of_pos_right _ (by positivity)
  have hm : 20 * u ^ 5 ≤ u ^ 6 := by
    calc
      _ ≤ u * u ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' u 5).symm
  omega

theorem execute_work (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) (right : Array (LeafRecord n)) {d : ℕ}
    (K : ℤ) (fuel : ℕ) (s : CountedParentJoin.State I F P mode right d)
    (buf : Array (CountedParentJoin.Child n)) (q budget : ℕ)
    (hn : 10000 ≤ n) (hd : d ≤ n) :
    (execute I F P mode right K fuel s buf q budget).2 ≤ budget + 1 := by
  have hnu : n ≤ inputScale I := by unfold inputScale; omega
  exact BudgetedFill.execute_work _ _ _ _ (inputScale I ^ 5) (inputScale I ^ 3)
    (6 * n + 4) (inputScale I ^ 6)
    (fun s => RepresentationKeys.read_scale I F P mode right s hd hn)
    (fun x => RepresentationKeys.pairKey_scale I F P mode x hn)
    CountedParentJoin.cells_le (iteration_charge hnu (hn.trans hnu)) _ _ _ _ _

end LowSpaceSubsetSum.BudgetedParentFill

end OAI
