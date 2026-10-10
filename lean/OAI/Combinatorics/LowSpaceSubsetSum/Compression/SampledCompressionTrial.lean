import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionSampleArrays
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionFromPermutation

namespace OAI

/-! # Compression from bounded random draws through the stopped residue scan

The sampled permutation is materialized and used by the domain constructor.
Every failure branch retains the work already performed. No ideal fallback
permutation or prime is evaluated to choose a runtime operation.
-/

noncomputable section

namespace LowSpaceSubsetSum.SampledCompressionTrial

variable {n : ℕ}

def allowance (D : CompressionData n) :=
  CompressionFromPermutation.charge n + 2 * trialWatchdog D.input

def run (D : CompressionData n) (hn : 168000000 ≤ n) (s : (D.sampler hn).Seed) :
    Bool × ℕ :=
  let sample := CompressionSampleArrays.run D hn s
  match sample.1 with
  | none => (false, sample.2 + 1)
  | some (v, q) =>
    let out := CompressionFromPermutation.run D v q (representationBufferCapacity n)
      (allowance D)
    (match out.1 with | none => false | some (yes, _) => yes, sample.2 + out.2 + 1)

theorem sound (D : CompressionData n) (hn : 168000000 ≤ n)
    (s : (D.sampler hn).Seed) (h : (run D hn s).1 = true) : Solvable D.input := by
  simp only [run] at h
  cases hs : (CompressionSampleArrays.run D hn s).1 with
  | none => simp only [hs, Bool.false_eq_true] at h
  | some p =>
    rcases p with ⟨v, q⟩
    simp only [hs] at h
    obtain ⟨e, _, hv⟩ := CompressionSampleArrays.value D hn s v q hs
    cases ho : (CompressionFromPermutation.run D v q (representationBufferCapacity n)
        (allowance D)).1 with
    | none => simp only [ho, Bool.false_eq_true] at h
    | some p =>
      rcases p with ⟨yes, rest⟩
      simp only [ho] at h
      subst yes
      exact CompressionFromPermutation.sound D v e hv q _ _ rest ho

theorem work (D : CompressionData n) (hn : 168000000 ≤ n) (s : (D.sampler hn).Seed) :
    (run D hn s).2 ≤ (n + 1) * n ^ 3 + SamplerExecution.primeTestBudget n +
      10 * (n + 1) ^ 2 + 3 + allowance D + 2 := by
  have hs := CompressionSampleArrays.work D hn s
  simp only [run]
  cases hv : (CompressionSampleArrays.run D hn s).1 with
  | none => dsimp only; omega
  | some p =>
    rcases p with ⟨v, q⟩
    obtain ⟨e, _, he⟩ := CompressionSampleArrays.value D hn s v q hv
    have ho := (CompressionFromPermutation.account D v e he q (by omega) (allowance D)).1
    dsimp only
    omega

theorem accepts (D : CompressionData n) (hn : 168000000 ≤ n)
    (s : (D.sampler hn).Seed) (h : CompressionSetup.TrialHistory n)
    (hs : (D.sampler hn).bounded s = some h)
    (hh : D.AcceptedWithCompactTests (representationBufferCapacity n) h) :
    (run D hn s).1 = true := by
  obtain ⟨v, hv, he⟩ := CompressionSampleArrays.complete D hn s h.1 h.2 hs
  obtain ⟨rest, hr⟩ := CompressionFromPermutation.accepts D v h.1 he h.2
    (representationBufferCapacity n) (by omega) hh.1 hh.2
  simp only [run, hv, allowance, hr]

theorem probability (D : CompressionData n) (hn : 168000000 ≤ n)
    (hsolve : Solvable D.input)
    (hmean : (153 / 20000 : ℝ) * n ≤
      meanDeficiency D.weights Finset.univ (compressionHalfSize n))
    (hlog : Real.logb 2 (inputScale D.input) ≤ (n : ℝ) / 1000000000) :
    (1 / 8 : ℝ) ≤ (D.sampler hn).law.probability (fun s => (run D hn s).1 = true) := by
  have h := D.bounded_compact_acceptance_probability (representationBufferCapacity n)
    hn hsolve hmean hlog
  rw [SamplerCoupling.boundedLaw, FiniteLaw.map_probability] at h
  apply h.trans
  apply FiniteLaw.probability_mono
  rintro s ⟨history, hs, hh⟩
  exact accepts D hn s history hs hh

end LowSpaceSubsetSum.SampledCompressionTrial

end

end OAI
