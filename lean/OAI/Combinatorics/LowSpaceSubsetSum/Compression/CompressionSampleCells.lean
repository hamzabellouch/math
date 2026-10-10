import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionSampleArrays
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationSamplerCells

namespace OAI

/-! # Live storage for the bounded compression sample

The accepted digits are materialized once. The prime candidate tuple is
retained, but not searched, when the digit sampler fails. Ideal backup
values remain proof data and do not select an execution branch.
-/

noncomputable section
namespace LowSpaceSubsetSum.CompressionSampleCells

variable {n : ℕ}

def run (D : CompressionData n) (hn : 168000000 ≤ n) (s : (D.sampler hn).Seed) :
    (Option (Vector (Fin n) n × CompressionSetup.PrimeSpace n) × ℕ) × ℕ :=
  let digits := PermutationSamplerCells.run n n s.1
  match digits.1.value with
  | none => ((none, digits.1.reads+digits.1.tests+1), digits.2+3*n^3+128)
  | some d =>
    let v := PermutationArray.build n d
    let q := SamplerVectorCells.primeSeed
      (show 4 ≤ compressionPrimeExponent n by unfold compressionPrimeExponent; omega) n s.2
    ((q.1.value.map (fun q => (v.1, q)),
        digits.1.reads+digits.1.tests+v.2+q.1.reads+q.1.tests+3),
      digits.2+PermutationArray.peakCells n+q.2+4*n+64)

theorem value (D : CompressionData n) (hn : 168000000 ≤ n) (s : (D.sampler hn).Seed) :
    (run D hn s).1 = CompressionSampleArrays.run D hn s := by
  simp only [run, CompressionSampleArrays.run, PermutationSamplerCells.run_value,
    SamplerVectorCells.primeSeed_value, CompressionSampleArrays.prime]
  split <;> simp_all only

theorem cells (D : CompressionData n) (hn : 168000000 ≤ n) (s : (D.sampler hn).Seed) :
    (run D hn s).2 ≤ (n+1)*(3*n^3+256) := by
  have hd := PermutationSamplerCells.run_cells n n s.1
  have hp := PermutationArray.peakCells_bound n
  have hq := SamplerVectorCells.primeSeed_cells
    (show 4 ≤ compressionPrimeExponent n by unfold compressionPrimeExponent; omega) n s.2
  simp only [run]
  split <;> dsimp only <;>
    nlinarith only [hd, hp, hq, Nat.zero_le (n^3)]

theorem cells_scale (D : CompressionData n) (hn : 168000000 ≤ n)
    (s : (D.sampler hn).Seed) : (run D hn s).2 ≤ inputScale D.input^5 := by
  have hu : n+1 ≤ inputScale D.input := by unfold inputScale; omega
  have hu0 : 10000 ≤ inputScale D.input := by omega
  have hc := Nat.pow_le_pow_left (show n ≤ inputScale D.input by omega) 3
  have hu3 : inputScale D.input ≤ inputScale D.input^3 := by
    simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ inputScale D.input)
      (by decide : 1 ≤ 3)
  have ht : 3*n^3+256 ≤ 4*inputScale D.input^3 := by
    nlinarith only [hc, hu0, hu3]
  have hm := Nat.mul_le_mul hu ht
  have hm' : (n+1)*(3*n^3+256) ≤ 4*inputScale D.input^4 := by
    convert hm using 1; ring
  have hp : 4*inputScale D.input^4 ≤ inputScale D.input^5 := by
    calc
      _ ≤ inputScale D.input*inputScale D.input^4 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  exact (cells D hn s).trans (hm'.trans hp)

end LowSpaceSubsetSum.CompressionSampleCells

end

end OAI
