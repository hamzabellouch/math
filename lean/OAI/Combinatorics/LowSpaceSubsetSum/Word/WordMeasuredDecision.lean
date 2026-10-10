import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedHistoryBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordDecisionUniform
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSampledAction

namespace OAI

/-! # Decision rounds with executed random-word generation

The finite-word experiment carries the work and peak storage of seed
generation, retained seeds, and the prepared actions.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordMeasuredDecision

variable {n : ℕ}

def asAction (r : WordSampledAction.Result) : (Bool × ℕ) × ℕ :=
  ((r.answer,r.work),r.cells)

def compression (I : Instance n) (hn : 168000000 ≤ n)
    (words : WordDecisionBranches.CompressionWords I) : (Bool × ℕ) × ℕ :=
  asAction (WordSampledAction.run
    (WordSeedMeasured.compression (CompressionData.mk I) hn (wordWidth I)
      ((Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le).trans (by
        unfold wordWidth inputScale; omega))
      (by unfold compressionPrimeExponent wordWidth inputScale; omega))
    (SampledCompressionCells.run (CompressionData.mk I) hn)
    (WordProgram.finiteStream words) 0)

def representationGenerator (I : Instance n) (hn : 10000 ≤ n) :
    WordSeedMeasured.Execution (WordDecisionBranches.representationSampler I hn) :=
  WordSeedMeasured.bucketHistory I hn (wordWidth I) (WordSamplingBounds.word_width I)

def representation (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (words : WordDecisionBranches.RepresentationWords I) : (Bool × ℕ) × ℕ :=
  asAction (WordSampledAction.run
    (representationGenerator I hn)
    (WordDecisionBranches.representationAction I hn hlog)
    (WordProgram.finiteStream words) 0)

private theorem execute_projection {α : Type} [Fintype α] {w N : ℕ}
    {S : SamplerCoupling α} (X : WordSeedRealization.Realization w N S)
    (a : S.Seed → (Bool × ℕ) × ℕ) (words : Fin N → Fin (2^w)) :
    WordSeedRealization.execute X (fun s => (a s).1.1) false words =
      (WordSeedRealization.execute X a ((false,1),8) words).1.1 := by
  unfold WordSeedRealization.execute
  split <;> rfl

theorem compression_value (I : Instance n) (hn : 168000000 ≤ n)
    (words : WordDecisionBranches.CompressionWords I) :
    (compression I hn words).1.1 = (WordDecisionBranches.compression I hn words).1.1 := by
  unfold compression asAction
  rw [WordSampledAction.finite_value,execute_projection]
  rfl

theorem representation_value (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (words : WordDecisionBranches.RepresentationWords I) :
    (representation I hn hlog words).1.1 =
      (WordDecisionBranches.representation I hn hlog words).1.1 := by
  have h := WordSampledAction.finite_value (representationGenerator I hn)
    (WordDecisionBranches.representationAction I hn hlog) words
  exact h.trans (execute_projection (WordDecisionBranches.representationSampler I hn)
    (WordDecisionBranches.representationAction I hn hlog) words)

def round (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (words : WordDecisionRound.Words I) : (Bool × ℕ) × ℕ :=
  WordDecisionRound.combine (compression I (by omega) words.1)
    (representation I (by omega) hlog words.2)

theorem round_value (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (words : WordDecisionRound.Words I) :
    (round I hn hlog words).1.1 = (WordDecisionRound.run I hn hlog words).1.1 := by
  change (_ || _) = (_ || _)
  rw [compression_value,representation_value]

def repeated (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : Fin (inputScale I^120) → WordDecisionRound.Words I) : (Bool × ℕ) × ℕ :=
  DecisionRepetitionCells.run (round I hn (roundLogBudget I (by omega) hscale)) words

theorem repeated_value (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : Fin (inputScale I^120) → WordDecisionRound.Words I) :
    (repeated I hn hscale words).1.1 =
      (WordDecisionRound.repeated I hn hscale words).1.1 := by
  simp only [repeated,WordDecisionRound.repeated,DecisionRepetitionCells.value,
    DecisionRepetition.value]
  congr 1
  funext x
  exact round_value I hn _ x

theorem sound (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : Fin (inputScale I^120) → WordDecisionRound.Words I)
    (hy : (repeated I hn hscale words).1.1 = true) : Solvable I :=
  WordDecisionRound.repeated_sound I hn hscale words ((repeated_value I hn hscale words).symm.trans hy)

theorem probability (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (hden : ((mixerSize n/2 : ℕ) : ℝ)+1 <
      (2 : ℝ)^((1/1500 : ℝ)*(mixerSize n/2 : ℕ))) (hs : Solvable I) :
    (2/3 : ℝ) <
      (FiniteLaw.uniform : FiniteLaw (Fin (inputScale I^120) → WordDecisionRound.Words I)).probability
        (fun words => (repeated I hn hscale words).1.1 = true) := by
  simp only [repeated_value]
  exact WordDecisionUniform.repeated_probability I hn hscale hden hs

end LowSpaceSubsetSum.WordMeasuredDecision

end

end OAI
