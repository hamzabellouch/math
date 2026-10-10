import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionFromPermutationCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionSampleCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.SampledCompressionTrial

namespace OAI

/-! # Every-outcome storage of the executed sampled compression trial

The trace includes the bounded candidate tuples, materialized permutation,
all guarded array construction, and the complete stopped residue scan.
The first projection preserves both the Boolean result and its work count.
-/

noncomputable section
namespace LowSpaceSubsetSum.SampledCompressionCells

variable {n : ℕ}

/-- Retained candidate words, input indices, permutation and scalar fields. -/
def retained (n : ℕ) := 32*(n+1)^4+256

def run (D : CompressionData n) (hn : 168000000 ≤ n) (s : (D.sampler hn).Seed) :
    (Bool × ℕ) × ℕ :=
  let sample := CompressionSampleCells.run D hn s
  match sample.1.1 with
  | none => ((false,sample.1.2+1),sample.2+retained n)
  | some (v,q) =>
    let out := CompressionFromPermutationCells.run D v q (representationBufferCapacity n)
      (SampledCompressionTrial.allowance D)
    ((match out.1.1 with | none => false | some (yes,_) => yes,
        sample.1.2+out.1.2+1),sample.2+out.2+retained n)

theorem value (D : CompressionData n) (hn : 168000000 ≤ n) (s : (D.sampler hn).Seed) :
    (run D hn s).1 = SampledCompressionTrial.run D hn s := by
  simp only [run,SampledCompressionTrial.run,CompressionSampleCells.value,
    CompressionFromPermutationCells.value]
  split <;> simp_all only
  rfl

private theorem retained_bound (D : CompressionData n) (hn : 10000 ≤ n) :
    retained n ≤ inputScale D.input^6 := by
  let u := inputScale D.input
  have hu : n+1 ≤ u := by unfold u inputScale; omega
  have hu0 : 10000 ≤ u := by omega
  have h4 := Nat.pow_le_pow_left hu 4
  have hbase : 1 ≤ u^4 := Nat.one_le_pow _ _ (by omega)
  have hcoef : 288 ≤ u^2 := by nlinarith only [hu0]
  have hm := Nat.mul_le_mul_right (u^4) hcoef
  have he : u^2*u^4 = u^6 := by rw [←pow_add]
  rw [he] at hm
  unfold retained
  change 32*(n+1)^4+256 ≤ u^6
  nlinarith only [h4,hbase,hm]

theorem cells (D : CompressionData n) (hn : 168000000 ≤ n) (s : (D.sampler hn).Seed) :
    (run D hn s).2 ≤ inputScale D.input^12*(compressionDictionaryCapacity n+1) := by
  let u := inputScale D.input
  let C := compressionDictionaryCapacity n
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hs := CompressionSampleCells.cells_scale D hn s
  have hr := retained_bound D (by omega)
  change (CompressionSampleCells.run D hn s).2 ≤ u^5 at hs
  change retained n ≤ u^6 at hr
  have h5 : u^5 ≤ u^11 := Nat.pow_le_pow_right (by omega) (by decide)
  have h6 : u^6 ≤ u^11 := Nat.pow_le_pow_right (by omega) (by decide)
  have hc : u^11 ≤ u^11*(C+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hstep : 3*(u^11*(C+1)) ≤ u^12*(C+1) := by
    calc
      _ ≤ u*(u^11*(C+1)) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [←Nat.mul_assoc,←pow_succ']
  change _ ≤ u^12*(C+1)
  dsimp only [C] at hc hstep ⊢
  unfold run
  dsimp only
  split
  · dsimp only
    nlinarith only [hs,hr,h5,h6,hc,hstep]
  next v q hsample =>
    have hsource : (CompressionSampleArrays.run D hn s).1 = some (v,q) := by
      rw [←CompressionSampleCells.value]
      exact hsample
    obtain ⟨e,_,hv⟩ := CompressionSampleArrays.value D hn s v q hsource
    have hb := CompressionFromPermutationCells.cells D v e hv (by omega) q
      (representationBufferCapacity n) (SampledCompressionTrial.allowance D)
      (representationBufferCapacity_le n)
    dsimp only
    nlinarith only [hs,hr,h5,h6,hc,hstep,hb]

end LowSpaceSubsetSum.SampledCompressionCells

end

end OAI
