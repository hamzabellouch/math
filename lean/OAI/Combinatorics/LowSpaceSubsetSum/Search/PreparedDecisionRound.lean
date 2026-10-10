import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationPreparedAcceptance
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.SampledCompressionTrial
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.FiniteRepetition

namespace OAI

/-! # A decision round executes both concrete stopped preparations -/

noncomputable section
namespace LowSpaceSubsetSum.PreparedDecisionRound

variable {n : ℕ}

abbrev Seed (I : Instance n) (hn : 180000000 ≤ n) :=
  ((CompressionData.mk I).sampler (by omega)).Seed ×
    ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling (by omega)).Seed

def law (I : Instance n) (hn : 180000000 ≤ n) : FiniteLaw (Seed I hn) :=
  ((CompressionData.mk I).sampler (by omega)).law.prod
    ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling (by omega)).law

def run (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : Seed I hn) : Bool × ℕ :=
  let c := SampledCompressionTrial.run (CompressionData.mk I) (by omega) s.1
  let r := RepresentationPreparedTrial.run I (by omega) hlog s.2 (2 * trialWatchdog I)
  let yes := match r.1 with | none => false | some (b, _) => b
  (c.1 || yes, c.2 + r.2 + 3)

theorem value (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : Seed I hn) :
    (run I hn hlog s).1 =
      ((SampledCompressionTrial.run (CompressionData.mk I) (by omega) s.1).1 ||
        RepresentationPreparedAcceptance.accept I (by omega) hlog s.2) := rfl

theorem sound (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : Seed I hn) (hy : (run I hn hlog s).1 = true) : Solvable I := by
  rw [value, Bool.or_eq_true] at hy
  rcases hy with hc | hr
  · exact SampledCompressionTrial.sound (CompressionData.mk I) (by omega) s.1 hc
  · exact RepresentationPreparedAcceptance.sound I (by omega) hlog s.2 hr

theorem probability (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hsolve : Solvable I)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ)))
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000) :
    1 / (inputScale I : ℝ) ^ 110 ≤ (law I hn).probability (fun s => (run I hn hlog s).1 = true) := by
  let C := CompressionData.mk I
  let D := canonicalRepresentationData I
  let P : (C.sampler (by omega)).Seed → Prop :=
    fun s => (SampledCompressionTrial.run C (by omega) s).1 = true
  let Q : (D.zeroSetup.bucketHistoryCoupling (by omega)).Seed → Prop :=
    fun s => RepresentationPreparedAcceptance.accept I (by omega) hlog s = true
  by_cases hm : (153 / 20000 : ℝ) * n ≤ meanDeficiency C.weights Finset.univ (compressionHalfSize n)
  · have hp := SampledCompressionTrial.probability C (by omega) hsolve hm hscale
    have hu : (2 : ℝ) ≤ inputScale I := by
      exact_mod_cast (show 2 ≤ inputScale I by unfold inputScale; omega)
    have hd : (8 : ℝ) ≤ (inputScale I : ℝ) ^ 110 :=
      (by norm_num : (8 : ℝ) ≤ 2 ^ 110).trans (pow_le_pow_left₀ (by norm_num) hu _)
    have hl : 1 / (inputScale I : ℝ) ^ 110 ≤ (C.sampler (by omega)).law.probability P :=
      (one_div_le_one_div_of_le (by norm_num) hd).trans hp
    apply hl.trans
    have h := FiniteLaw.prod_or_ge_left (C.sampler (by omega)).law
      (D.zeroSetup.bucketHistoryCoupling (by omega)).law P Q
    simpa only [law, value, Bool.or_eq_true, C, D, P, Q] using h
  · have hm' : meanDeficiency D.zeroSetup.originalWeights Finset.univ (mixerSize n / 2) <
        (153 / 20000 : ℝ) * n := lt_of_not_ge hm
    have hp := RepresentationPreparedAcceptance.probability I hn hlog hsolve hm' hden hscale
    apply hp.trans
    have h := FiniteLaw.prod_or_ge_right (C.sampler (by omega)).law
      (D.zeroSetup.bucketHistoryCoupling (by omega)).law P Q
    simpa only [law, value, Bool.or_eq_true, C, D, P, Q] using h

theorem repeated_sound (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : Fin (inputScale I ^ 120) → Seed I hn)
    (hy : repeatAccept (fun s => (run I hn hlog s).1) s = true) : Solvable I :=
  repeatAccept_sound _ _ (sound I hn hlog) s hy

theorem repeated_probability (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hsolve : Solvable I)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ)))
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000) :
    (2 / 3 : ℝ) < ((law I hn).iid (inputScale I ^ 120)).probability
      (fun s => repeatAccept (fun s => (run I hn hlog s).1) s = true) :=
  repetition_acceptance_probability _ _ (by unfold inputScale; omega)
    (probability I hn hlog hsolve hden hscale)

end LowSpaceSubsetSum.PreparedDecisionRound

end

end OAI
