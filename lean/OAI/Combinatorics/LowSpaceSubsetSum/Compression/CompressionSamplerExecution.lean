import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSamplerExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionSamplerCoupling

namespace OAI

/-! # Executed bounded permutation and prime draws for compression -/

noncomputable section

namespace LowSpaceSubsetSum.CompressionData

variable {n : ℕ} (D : CompressionData n)

def samplerExecution (hn : 168000000 ≤ n) : SamplerExecution.Execution (D.sampler hn) :=
  SamplerExecution.bind (SamplerExecution.permutation n n) _ _
    (fun _ => SamplerExecution.prime (by unfold compressionPrimeExponent; omega) n)

theorem samplerExecution_bounded (hn : 168000000 ≤ n) :
    (D.samplerExecution hn).Bounded (n * n ^ 3 + n ^ 3) (SamplerExecution.primeTestBudget n) := by
  have hp := SamplerExecution.permutation_bounded n n
  have hq := SamplerExecution.prime_bounded
    (show 4 ≤ compressionPrimeExponent n by unfold compressionPrimeExponent; omega) n
  have hq' := hq.mono le_rfl (Nat.mul_le_mul_left (n ^ 3)
    (Nat.pow_le_pow_right (by decide) (show
      (compressionPrimeExponent n + 1) / 2 ≤ (n + 1) / 2 by
        unfold compressionPrimeExponent
        omega)))
  intro s
  have hb := SamplerExecution.bind_bounded (SamplerExecution.permutation n n) _ _
    (fun _ => SamplerExecution.prime (by unfold compressionPrimeExponent; omega) n)
    hp (fun _ => hq')
  simpa only [samplerExecution, SamplerExecution.primeTestBudget, Nat.zero_add] using hb s

theorem samplerExecution_operations (hn : 168000000 ≤ n) (s : (D.sampler hn).Seed) :
    ((D.samplerExecution hn).run s).reads + ((D.samplerExecution hn).run s).tests ≤
      3 * inputScale D.input ^ 4 * 2 ^ ((n + 1) / 2) := by
  have h := D.samplerExecution_bounded hn s
  have hu : n ≤ inputScale D.input := by unfold inputScale; omega
  have hu1 : 1 ≤ inputScale D.input := by unfold inputScale; omega
  have h3 := Nat.pow_le_pow_left hu 3
  have h34 : inputScale D.input ^ 3 ≤ inputScale D.input ^ 4 :=
    pow_le_pow_right' hu1 (by decide)
  have h4 : n * n ^ 3 ≤ inputScale D.input ^ 4 := by
    have hm := Nat.mul_le_mul hu h3
    simpa only [← pow_succ'] using hm
  have hread : n * n ^ 3 + n ^ 3 ≤ 2 * inputScale D.input ^ 4 := by omega
  have hT : 1 ≤ 2 ^ ((n + 1) / 2) := Nat.one_le_two_pow
  have hreads : n * n ^ 3 + n ^ 3 ≤ 2 * inputScale D.input ^ 4 * 2 ^ ((n + 1) / 2) :=
    hread.trans (Nat.le_mul_of_pos_right _ (by omega))
  have htests := Nat.mul_le_mul_right (2 ^ ((n + 1) / 2)) (h3.trans h34)
  unfold SamplerExecution.primeTestBudget at h
  nlinarith only [h.1, h.2, hreads, htests]

end LowSpaceSubsetSum.CompressionData

end

end OAI
