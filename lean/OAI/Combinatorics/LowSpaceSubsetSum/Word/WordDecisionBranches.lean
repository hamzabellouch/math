import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationTrialCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.SampledCompressionCells
import OAI.Combinatorics.LowSpaceSubsetSum.Search.PreparedDecisionWork
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.DecisionRepetitionCells
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedHistory
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSamplingBounds

namespace OAI

/-! # The two prepared branches driven by finite fair-word streams

The returned work counter measures the prepared action. The number of words
read by seed generation has its own bound; generation arithmetic is separate.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordDecisionBranches

variable {n : ℕ}

def compressionSampler (I : Instance n) (hn : 168000000 ≤ n) :=
  WordSeedRealization.compression (CompressionData.mk I) hn (wordWidth I)
    ((Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le).trans (by
      unfold wordWidth inputScale; omega))
    (by unfold compressionPrimeExponent wordWidth inputScale; omega)

def representationSampler (I : Instance n) (hn : 10000 ≤ n) :=
  WordSeedRealization.bucketHistory (canonicalRepresentationData I).zeroSetup hn
    (wordWidth I) (WordSamplingBounds.word_width I)

abbrev CompressionWords (I : Instance n) := Fin (n*n^3+n^3) → Fin (2^wordWidth I)
abbrev RepresentationWords (I : Instance n) :=
  Fin (WordRealization.historyReads n) → Fin (2^wordWidth I)

def compression (I : Instance n) (hn : 168000000 ≤ n) (words : CompressionWords I) :=
  WordSeedRealization.execute (compressionSampler I hn)
    (SampledCompressionCells.run (CompressionData.mk I) hn) ((false,1),8) words

def representationAction (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed) :=
  let out := RepresentationTrialCells.run I hn hlog s (2*trialWatchdog I)
  ((match out.1.1 with | none => false | some (yes,_) => yes,out.1.2),out.2)

def representation (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (words : RepresentationWords I) :=
  WordSeedRealization.execute (representationSampler I hn)
    (representationAction I hn hlog) ((false,1),8) words

theorem representationAction_value (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed) :
    (representationAction I hn hlog s).1.1 =
      RepresentationPreparedAcceptance.accept I hn hlog s := by
  change (match (RepresentationTrialCells.run I hn hlog s (2*trialWatchdog I)).1.1 with
    | none => false | some (yes,_) => yes) = _
  rw [RepresentationTrialCells.value]
  rfl

theorem compression_value (I : Instance n) (hn : 168000000 ≤ n)
    (words : CompressionWords I) :
    (compression I hn words).1.1 = WordSeedRealization.execute (compressionSampler I hn)
      (fun s => (SampledCompressionTrial.run (CompressionData.mk I) hn s).1) false words := by
  unfold compression WordSeedRealization.execute
  split
  · rfl
  · exact congrArg Prod.fst (SampledCompressionCells.value _ _ _)

theorem representation_value (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (words : RepresentationWords I) :
    (representation I hn hlog words).1.1 =
      WordSeedRealization.execute (representationSampler I hn)
        (RepresentationPreparedAcceptance.accept I hn hlog) false words := by
  unfold representation
  cases h : (WordSeedRealization.run (representationSampler I hn) words).1 with
  | none => simp only [WordSeedRealization.execute,h]
  | some s =>
    simp only [WordSeedRealization.execute,h]
    exact representationAction_value I hn hlog s.val

theorem compression_sound (I : Instance n) (hn : 168000000 ≤ n)
    (words : CompressionWords I) (hy : (compression I hn words).1.1 = true) : Solvable I := by
  rw [compression_value] at hy
  unfold WordSeedRealization.execute at hy
  split at hy
  · contradiction
  · exact SampledCompressionTrial.sound _ _ _ hy

theorem representation_sound (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (words : RepresentationWords I)
    (hy : (representation I hn hlog words).1.1 = true) : Solvable I := by
  rw [representation_value] at hy
  unfold WordSeedRealization.execute at hy
  split at hy
  · contradiction
  · exact RepresentationPreparedAcceptance.sound _ _ _ _ hy

theorem compression_probability (I : Instance n) (hn : 168000000 ≤ n)
    (hs : Solvable I)
    (hm : (153/20000 : ℝ)*n ≤
      meanDeficiency (CompressionData.mk I).weights Finset.univ (compressionHalfSize n))
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000) :
    (1/8 : ℝ) ≤ (FiniteLaw.uniform : FiniteLaw (CompressionWords I)).probability
      (fun words => (compression I hn words).1.1 = true) := by
  simp only [compression_value]
  apply ((CompressionData.mk I).bounded_compact_acceptance_probability
    (representationBufferCapacity n) hn hs hm hscale).trans
  exact WordSeedRealization.probability_success (compressionSampler I hn)
    (fun s => (SampledCompressionTrial.run (CompressionData.mk I) hn s).1)
    ((CompressionData.mk I).AcceptedWithCompactTests (representationBufferCapacity n))
    (SampledCompressionTrial.accepts (CompressionData.mk I) hn)

theorem representation_probability (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (hs : Solvable I)
    (hm : meanDeficiency (canonicalRepresentationData I).zeroSetup.originalWeights
      Finset.univ (mixerSize n/2) < (153/20000 : ℝ)*n)
    (hden : ((mixerSize n/2 : ℕ) : ℝ)+1 <
      (2 : ℝ)^((1/1500 : ℝ)*(mixerSize n/2 : ℕ)))
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000) :
    1/(inputScale I : ℝ)^110 ≤
      (FiniteLaw.uniform : FiniteLaw (RepresentationWords I)).probability
        (fun words => (representation I (by omega) hlog words).1.1 = true) := by
  obtain ⟨solution,hsolution⟩ := hs
  let D := canonicalRepresentationData I
  let R : RepresentationSetup n := ⟨I,solution,hsolution,D.mixers,D.disjoint,D.card⟩
  have hp := R.bounded_runtime_core_probability hn hm hden hscale
    (representationBufferCapacity n)
  apply hp.trans
  simp only [representation_value]
  exact WordSeedRealization.probability_success (representationSampler I (by omega))
    (RepresentationPreparedAcceptance.accept I (by omega) hlog)
    (D.CoreFavorable (by omega) hlog (representationBufferCapacity n))
    (RepresentationPreparedAcceptance.of_core I (by omega) hlog)

end LowSpaceSubsetSum.WordDecisionBranches

end

end OAI
