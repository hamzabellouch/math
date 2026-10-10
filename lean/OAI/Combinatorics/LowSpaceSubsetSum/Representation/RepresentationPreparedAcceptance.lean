import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationPreparedTrial

namespace OAI

/-! # Passing the favorable-event mass to the executed stored trial -/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationPreparedAcceptance

variable {n : ℕ}

def accept (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed) : Bool :=
  match (RepresentationPreparedTrial.run I hn hlog s (2 * trialWatchdog I)).1 with
  | none => false
  | some (yes, _) => yes

theorem of_core (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed)
    (history : (canonicalRepresentationData I).zeroSetup.BucketTrialHistory (by omega))
    (hs : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).bounded s = some history)
    (hh : (canonicalRepresentationData I).CoreFavorable hn hlog (representationBufferCapacity n) history) :
    accept I hn hlog s = true := by
  obtain ⟨rest, hr⟩ := RepresentationPreparedTrial.accepts I hn hlog s history hs hh
  simp only [accept, hr]

theorem sound (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed)
    (hy : accept I hn hlog s = true) : Solvable I := by
  cases hv : (RepresentationPreparedTrial.run I hn hlog s (2 * trialWatchdog I)).1 with
  | none => simp only [accept, hv, Bool.false_eq_true] at hy
  | some pair =>
    rcases pair with ⟨b, rest⟩
    have hb : b = true := by simpa only [accept, hv] using hy
    subst b
    exact RepresentationPreparedTrial.sound I hn hlog s (2 * trialWatchdog I) rest hv

theorem probability_ge_core (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) :
    ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).boundedLaw.probability
      (fun o => ∃ history, o = some history ∧
        (canonicalRepresentationData I).CoreFavorable hn hlog (representationBufferCapacity n) history) ≤
    ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).law.probability
      (fun s => accept I hn hlog s = true) := by
  rw [SamplerCoupling.boundedLaw, FiniteLaw.map_probability]
  apply FiniteLaw.probability_mono
  rintro s ⟨history, hs, hh⟩
  exact of_core I hn hlog s history hs hh

theorem probability (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hsolve : Solvable I)
    (hmean : meanDeficiency (canonicalRepresentationData I).zeroSetup.originalWeights
      Finset.univ (mixerSize n / 2) < (153 / 20000 : ℝ) * n)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ)))
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000) :
    1 / (inputScale I : ℝ) ^ 110 ≤
      ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling (by omega)).law.probability
        (fun s => accept I (by omega) hlog s = true) := by
  obtain ⟨solution, hsolution⟩ := hsolve
  let D := canonicalRepresentationData I
  let R : RepresentationSetup n :=
    ⟨I, solution, hsolution, D.mixers, D.disjoint, D.card⟩
  have hp := R.bounded_runtime_core_probability hn hmean hden hscale
    (representationBufferCapacity n)
  exact hp.trans (probability_ge_core I (by omega) hlog)

end LowSpaceSubsetSum.RepresentationPreparedAcceptance

end

end OAI
