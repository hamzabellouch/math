import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationSamplerCoupling
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionSoundness

namespace OAI

/-! # Input-only bounded permutation and prime draws for compression -/

noncomputable section

namespace LowSpaceSubsetSum.CompressionData

variable {n : ℕ} (D : CompressionData n)

/-- Compression draws one permutation and one prime. Its residue counter is
enumerated deterministically by `compressionTrial`. -/
def sampler (_D : CompressionData n) (hn : 168000000 ≤ n) :
    SamplerCoupling (CompressionSetup.TrialHistory n) :=
  (permutationCoupling n n).bind (fun _ => CompressionSetup.PrimeSpace n)
    (fun _ => primeCoupling (by unfold compressionPrimeExponent; omega) n)

theorem sampler_uniform (hn : 168000000 ≤ n) :
    (D.sampler hn).idealLaw = D.trialLaw hn := by
  rw [sampler, SamplerCoupling.bind_idealLaw, permutationCoupling_uniform]
  simp only [primeCoupling_uniform]
  rfl

theorem sampler_failure (hn : 168000000 ≤ n) :
    (D.sampler hn).failure ≤ n / (2 : ℝ) ^ (n ^ 3) + Real.exp (-((n : ℝ) ^ 2 / 4)) := by
  have hprime : compressionPrimeExponent n ≤ n := by
    unfold compressionPrimeExponent
    omega
  have h := SamplerCoupling.bind_failure_le (permutationCoupling n n)
    (fun _ => CompressionSetup.PrimeSpace n)
    (fun _ => primeCoupling (by unfold compressionPrimeExponent; omega) n)
    (Real.exp (-((n : ℝ) ^ 2 / 4))) (fun _ => primeCoupling_failure _ hprime)
  exact h.trans (add_le_add (permutationCoupling_failure n n) le_rfl)

private theorem prime_tail (hn : 168000000 ≤ n) :
    Real.exp (-((n : ℝ) ^ 2 / 4)) ≤ 1 / (2 : ℝ) ^ (2 * n) := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast (show 16 ≤ n by omega)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ (2 * n) ≤ Real.exp ((n : ℝ) ^ 2 / 4) := by
    calc
      _ ≤ (Real.exp 1) ^ (2 * n) := pow_le_pow_left₀ (by norm_num) htwo _
      _ = Real.exp ((2 * n : ℕ) : ℝ) := by rw [← Real.exp_nat_mul]; simp
      _ ≤ _ := Real.exp_le_exp.mpr (by push_cast; nlinarith)
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hp

theorem sampler_failure_pow (hn : 168000000 ≤ n) :
    (D.sampler hn).failure ≤ 1 / (2 : ℝ) ^ n := by
  have hcube : 3 * n ≤ n ^ 3 := by
    have hs : 3 ≤ n ^ 2 := by nlinarith [show 16 ≤ n by omega]
    calc
      3 * n ≤ n ^ 2 * n := Nat.mul_le_mul_right n hs
      _ = n ^ 3 := by ring
  have hrange : (n : ℝ) / (2 : ℝ) ^ (n ^ 3) ≤ 1 / (2 : ℝ) ^ (2 * n) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [one_mul]
    calc
      _ ≤ (2 : ℝ) ^ n * 2 ^ (2 * n) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le)
          (by positivity)
      _ = (2 : ℝ) ^ (3 * n) := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hcube
  have hp := prime_tail hn
  have hb := D.sampler_failure hn
  have htwo : (2 : ℝ) ≤ 2 ^ n := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ n)
  calc
    _ ≤ 2 / (2 : ℝ) ^ (2 * n) := by
      simp only [div_eq_mul_inv, one_mul] at hrange hp hb ⊢
      linarith
    _ ≤ 1 / (2 : ℝ) ^ n := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      rw [one_mul, two_mul n, pow_add]
      exact mul_le_mul_of_nonneg_right htwo (by positivity)

/-- Every ideal compression event loses at most the unconditional exhaustion
probability. No event is conditioned on successful sampling. -/
theorem sampler_event (hn : 168000000 ≤ n)
    (P : CompressionSetup.TrialHistory n → Prop) :
    (D.trialLaw hn).probability P - 1 / (2 : ℝ) ^ n ≤
      (D.sampler hn).boundedLaw.probability (fun o => ∃ h, o = some h ∧ P h) := by
  have h := (D.sampler hn).event_lower P
  rw [D.sampler_uniform hn] at h
  exact (sub_le_sub_left (D.sampler_failure_pow hn) _).trans h

end LowSpaceSubsetSum.CompressionData

end

end OAI
