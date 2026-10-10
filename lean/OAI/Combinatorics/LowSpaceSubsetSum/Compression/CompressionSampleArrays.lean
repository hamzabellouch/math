import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationDigitsExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionSamplerExecution

namespace OAI

/-! # Executing compression sampling into stored input arrays

Only accepted range digits are materialized. The prime draw is skipped when
the permutation sampler exhausts its allowance. Ideal backup values occur
only in the refinement proof, never as a runtime choice.
-/

noncomputable section

namespace LowSpaceSubsetSum.CompressionSampleArrays

variable {n : ℕ}

def prime (hn : 168000000 ≤ n) :=
  SamplerExecution.prime (show 4 ≤ compressionPrimeExponent n by
    unfold compressionPrimeExponent; omega) n

def run (D : CompressionData n) (hn : 168000000 ≤ n) (s : (D.sampler hn).Seed) :
    Option (Vector (Fin n) n × CompressionSetup.PrimeSpace n) × ℕ :=
  let digits := PermutationDigitsExecution.run n n s.1
  match digits.value with
  | none => (none, digits.reads + digits.tests + 1)
  | some d =>
    let v := PermutationArray.build n d
    let q := (prime hn).run s.2
    (q.value.map (fun q => (v.1, q)),
      digits.reads + digits.tests + v.2 + q.reads + q.tests + 3)

theorem value (D : CompressionData n) (hn : 168000000 ≤ n) (s : (D.sampler hn).Seed)
    (v : Vector (Fin n) n) (q : CompressionSetup.PrimeSpace n)
    (h : (run D hn s).1 = some (v, q)) :
    ∃ e, (D.sampler hn).bounded s = some ⟨e, q⟩ ∧ ∀ i : Fin n, v[i.val] = e i := by
  rcases s with ⟨first, second⟩
  simp only [run] at h
  cases hd : (PermutationDigitsExecution.run n n first).value with
  | none => simp only [hd, reduceCtorEq] at h
  | some d =>
    simp only [hd] at h
    obtain ⟨q', hq, heq⟩ := Option.map_eq_some_iff.mp h
    cases heq
    refine ⟨PermutationArray.semantic n d, ?_, PermutationArray.build_value n d⟩
    have hp := PermutationDigitsExecution.value n n first
    rw [hd] at hp
    have hp' : (permutationCoupling n n).bounded first =
        some (PermutationArray.semantic n d) := by
      rw [← (SamplerExecution.permutation n n).value_eq]
      exact hp.symm
    have hi := (SamplerExecution.permutation n n).ideal_eq_of_some first
      (PermutationArray.semantic n d) hp.symm
    have hq' := (prime hn).value_eq second
    rw [hq] at hq'
    simp only [CompressionData.sampler, SamplerCoupling.bind, hp', reduceCtorEq, ↓reduceIte]
    rw [← hq', hi]
    rfl

theorem complete (D : CompressionData n) (hn : 168000000 ≤ n) (s : (D.sampler hn).Seed)
    (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (h : (D.sampler hn).bounded s = some ⟨e, q⟩) :
    ∃ v, (run D hn s).1 = some (v, q) ∧ ∀ i : Fin n, v[i.val] = e i := by
  rcases s with ⟨first, second⟩
  have hp := PermutationDigitsExecution.value n n first
  cases hd : (PermutationDigitsExecution.run n n first).value with
  | none =>
    rw [hd] at hp
    have hp' : (permutationCoupling n n).bounded first = none := by
      rw [← (SamplerExecution.permutation n n).value_eq]
      exact hp.symm
    simp only [CompressionData.sampler, SamplerCoupling.bind, hp', ↓reduceIte,
      reduceCtorEq] at h
  | some d =>
    rw [hd] at hp
    have hp' : (permutationCoupling n n).bounded first =
        some (PermutationArray.semantic n d) := by
      rw [← (SamplerExecution.permutation n n).value_eq]
      exact hp.symm
    have hi := (SamplerExecution.permutation n n).ideal_eq_of_some first
      (PermutationArray.semantic n d) hp.symm
    simp only [CompressionData.sampler, SamplerCoupling.bind, hp', reduceCtorEq,
      ↓reduceIte] at h
    obtain ⟨q', hq, heq⟩ := Option.map_eq_some_iff.mp h
    have he : PermutationArray.semantic n d = e := by
      exact hi.symm.trans (congrArg Sigma.fst heq)
    have heq' : q' = q := by
      exact congrArg (fun h : CompressionSetup.TrialHistory n => h.2) heq
    subst q'
    refine ⟨(PermutationArray.build n d).1, ?_, ?_⟩
    · have hq' := (prime hn).value_eq second
      rw [hq] at hq'
      simp only [run, hd, hq', Option.map_some]
    · rw [← he]
      exact PermutationArray.build_value n d

theorem work (D : CompressionData n) (hn : 168000000 ≤ n) (s : (D.sampler hn).Seed) :
    (run D hn s).2 ≤ (n + 1) * n ^ 3 + SamplerExecution.primeTestBudget n +
      10 * (n + 1) ^ 2 + 3 := by
  have hd := PermutationDigitsExecution.counts n n s.1
  have hq := SamplerExecution.prime_bounded
    (show 4 ≤ compressionPrimeExponent n by unfold compressionPrimeExponent; omega) n s.2
  have he : (compressionPrimeExponent n + 1) / 2 ≤ (n + 1) / 2 := by
    unfold compressionPrimeExponent; omega
  have ht : n ^ 3 * 2 ^ ((compressionPrimeExponent n + 1) / 2) ≤
      n ^ 3 * 2 ^ ((n + 1) / 2) :=
    Nat.mul_le_mul_left (n ^ 3) (Nat.pow_le_pow_right (by decide) he)
  simp only [run]
  split
  · dsimp only
    nlinarith only [hd.1, hd.2]
  next d _ =>
    have hv := PermutationArray.build_work n d
    change _ + _ + _ + _ + _ + 3 ≤ _
    unfold prime SamplerExecution.primeTestBudget
    nlinarith only [hd.1, hd.2, hq.1, hq.2, ht, hv]

end LowSpaceSubsetSum.CompressionSampleArrays

end

end OAI
