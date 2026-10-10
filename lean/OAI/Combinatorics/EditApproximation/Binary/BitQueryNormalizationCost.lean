import OAI.Combinatorics.EditApproximation.Binary.BitRankedNormalize
import OAI.Combinatorics.EditApproximation.Binary.BitMemoWork

namespace OAI

namespace EditApproximation.BitQuery

theorem normalize_work_bound {ι : Type*} (program : BitQuery ι BinaryFraction)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining A B C : ℕ)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (ha : (program.value oracle).width ≤ A) (hb : base.length ≤ B)
    (hc : program.work oracle readWork ≤ C) :
    (program.normalize base hbase remaining).work oracle readWork ≤
      C + BinaryFraction.powerDenominatorBitBudget remaining A B + 1 := by
  rw [normalize_work]
  have h := BinaryFraction.powerDenominatorWithWork_cost (program.value oracle) base hbase remaining A B ha hb
  change program.work oracle readWork + (0 + _ + 1) ≤ _
  dsimp only
  omega

end EditApproximation.BitQuery

namespace EditApproximation

theorem rankedNormalizeBody_localWork_bound {κ : Type*} (rank : κ → ℕ)
    (raw : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining A C : κ → ℕ)
    (B : ℕ) (hb : base.length ≤ B) (key : κ)
    (ha : ((raw key).value (fun child => rankedBitProgramValue rank
      (rankedNormalizeBody rank raw base hbase remaining) child.val)).width ≤ A key)
    (hc : (raw key).work (fun child => rankedBitProgramValue rank
      (rankedNormalizeBody rank raw base hbase remaining) child.val) (fun _ => 0) ≤ C key) :
    rankedBitLocalWork rank (rankedNormalizeBody rank raw base hbase remaining) key ≤
      C key + BinaryFraction.powerDenominatorBitBudget (remaining key) (A key) B + 1 :=
  BitQuery.normalize_work_bound (raw key) base hbase (remaining key) (A key) B (C key) _ _ ha hb hc

end EditApproximation

end OAI
