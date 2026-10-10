import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionPreparedCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ResidueLoopCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.BudgetedCompressionSchedule

namespace OAI

/-! # Reusing one compression workspace throughout the residue loop -/

namespace LowSpaceSubsetSum.CompressionScheduleCells

open PreparedCompressionPass (Arrays)
variable {n : ℕ}

def bucket (I : Instance n) (C B : ℕ) (A : Arrays) (P : ℕ) (hP : 0 < P)
    (z budget : ℕ) :=
  if z < P then
    CompressionPreparedCells.run I C B A P I.target z (by exact_mod_cast hP) budget
  else ((some (false,budget),0),8)

theorem bucket_value (I : Instance n) (C B : ℕ) (A : Arrays) (P : ℕ) (hP : 0 < P)
    (z budget : ℕ) : (bucket I C B A P hP z budget).1 =
      BudgetedCompressionSchedule.bucket I C B A P hP z budget := by
  unfold bucket BudgetedCompressionSchedule.bucket
  split
  · exact CompressionPreparedCells.value I C B A P I.target z _ budget
  · rfl

def run (I : Instance n) (C B : ℕ) (A : Arrays) (P : ℕ) (hP : 0 < P) (budget : ℕ) :=
  let out := ResidueLoopCells.run (bucket I C B A P hP) 0 P budget
  (out.1,out.2+4*PreparedCompressionPass.size A+32)

theorem value (I : Instance n) (C B : ℕ) (A : Arrays) (P : ℕ) (hP : 0 < P) (budget : ℕ) :
    (run I C B A P hP budget).1 = BudgetedCompressionSchedule.run I C B A P hP budget := by
  rw [run,ResidueLoopCells.value]
  have he : (fun z b => (bucket I C B A P hP z b).1) =
      BudgetedCompressionSchedule.bucket I C B A P hP := by
    funext z b
    exact bucket_value I C B A P hP z b
  rw [he]
  rfl

theorem cells (I : Instance n) (hn : 10000 ≤ n) (C B : ℕ) (A : Arrays)
    (P : ℕ) (hP : 0 < P) (budget : ℕ) (hB : B ≤ C)
    (hL : ∀ i, (A.first i).size ≤ C) (hR : ∀ i, (A.second i).size ≤ C) (hC : C ≤ 2^n) :
    (run I C B A P hP budget).2 ≤ inputScale I^9*(C+1) := by
  let u := inputScale I
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hlarge : 100 ≤ u^8 := by
    have hp : u ≤ u^8 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ u by omega) (by decide : 1 ≤ 8)
    omega
  have hb (z b : ℕ) : (bucket I C B A P hP z b).2 ≤ u^8*(C+1) := by
    unfold bucket
    split
    · exact CompressionPreparedCells.cells I hn C B A P I.target z _ b hB hL hR hC
    · dsimp only; nlinarith only [hlarge]
  have h := ResidueLoopCells.cells (bucket I C B A P hP) (u^8*(C+1)) hb 0 P budget
  have hs := CompressionPreparedCells.arrays_size A C hL hR
  have hm : 2*u^8*(C+1) ≤ u^9*(C+1) := by
    apply Nat.mul_le_mul_right
    calc
      _ ≤ u*u^8 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  change _+4*PreparedCompressionPass.size A+32 ≤ _
  nlinarith only [h,hs,hlarge,hm]

end LowSpaceSubsetSum.CompressionScheduleCells

end OAI
