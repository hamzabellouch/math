import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordDecisionBranches
import OAI.Combinatorics.LowSpaceSubsetSum.Search.DecisionRound

namespace OAI

/-! # Independent fair-word rounds and counter-executed amplification -/

noncomputable section
namespace LowSpaceSubsetSum.WordDecisionRound

variable {n : ℕ}

abbrev Words (I : Instance n) :=
  WordDecisionBranches.CompressionWords I × WordDecisionBranches.RepresentationWords I

def law (I : Instance n) : FiniteLaw (Words I) :=
  (FiniteLaw.uniform : FiniteLaw (WordDecisionBranches.CompressionWords I)).prod
    (FiniteLaw.uniform : FiniteLaw (WordDecisionBranches.RepresentationWords I))

def combine (c r : (Bool × ℕ) × ℕ) : (Bool × ℕ) × ℕ :=
  ((c.1.1 || r.1.1,c.1.2+r.1.2+3),max c.2 (r.2+8)+16)

def run (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (words : Words I) : (Bool × ℕ) × ℕ :=
  combine (WordDecisionBranches.compression I (by omega) words.1)
    (WordDecisionBranches.representation I (by omega) hlog words.2)

theorem value (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (words : Words I) :
    (run I hn hlog words).1.1 =
      ((WordDecisionBranches.compression I (by omega) words.1).1.1 ||
        (WordDecisionBranches.representation I (by omega) hlog words.2).1.1) := rfl

theorem sound (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (words : Words I) (hy : (run I hn hlog words).1.1 = true) : Solvable I := by
  rw [value,Bool.or_eq_true] at hy
  rcases hy with hc | hr
  · exact WordDecisionBranches.compression_sound I (by omega) words.1 hc
  · exact WordDecisionBranches.representation_sound I (by omega) hlog words.2 hr

theorem probability (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (hs : Solvable I)
    (hden : ((mixerSize n/2 : ℕ) : ℝ)+1 <
      (2 : ℝ)^((1/1500 : ℝ)*(mixerSize n/2 : ℕ)))
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000) :
    1/(inputScale I : ℝ)^110 ≤
      (law I).probability (fun words => (run I hn hlog words).1.1 = true) := by
  let P : WordDecisionBranches.CompressionWords I → Prop := fun words =>
    (WordDecisionBranches.compression I (by omega) words).1.1 = true
  let Q : WordDecisionBranches.RepresentationWords I → Prop := fun words =>
    (WordDecisionBranches.representation I (by omega) hlog words).1.1 = true
  by_cases hm : (153/20000 : ℝ)*n ≤
      meanDeficiency (CompressionData.mk I).weights Finset.univ (compressionHalfSize n)
  · have hp := WordDecisionBranches.compression_probability I (by omega) hs hm hscale
    have hu : (2 : ℝ) ≤ inputScale I := by
      exact_mod_cast (show 2 ≤ inputScale I by unfold inputScale; omega)
    have hd : (8 : ℝ) ≤ (inputScale I : ℝ)^110 :=
      (by norm_num : (8 : ℝ) ≤ 2^110).trans (pow_le_pow_left₀ (by norm_num) hu _)
    apply ((one_div_le_one_div_of_le (by norm_num) hd).trans hp).trans
    simpa only [law,value,Bool.or_eq_true,P,Q] using
      FiniteLaw.prod_or_ge_left
        (FiniteLaw.uniform : FiniteLaw (WordDecisionBranches.CompressionWords I))
        (FiniteLaw.uniform : FiniteLaw (WordDecisionBranches.RepresentationWords I)) P Q
  · have hm' : meanDeficiency (canonicalRepresentationData I).zeroSetup.originalWeights
        Finset.univ (mixerSize n/2) < (153/20000 : ℝ)*n := lt_of_not_ge hm
    apply (WordDecisionBranches.representation_probability I hn hlog hs hm' hden hscale).trans
    simpa only [law,value,Bool.or_eq_true,P,Q] using
      FiniteLaw.prod_or_ge_right
        (FiniteLaw.uniform : FiniteLaw (WordDecisionBranches.CompressionWords I))
        (FiniteLaw.uniform : FiniteLaw (WordDecisionBranches.RepresentationWords I)) P Q

def repeated (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : Fin (inputScale I^120) → Words I) : (Bool × ℕ) × ℕ :=
  DecisionRepetitionCells.run (run I hn (roundLogBudget I (by omega) hscale)) words

theorem repeated_sound (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : Fin (inputScale I^120) → Words I)
    (hy : (repeated I hn hscale words).1.1 = true) : Solvable I := by
  rw [repeated,DecisionRepetitionCells.value,DecisionRepetition.value] at hy
  exact repeatAccept_sound _ _ (sound I hn _) words hy

theorem repeated_probability (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (hden : ((mixerSize n/2 : ℕ) : ℝ)+1 <
      (2 : ℝ)^((1/1500 : ℝ)*(mixerSize n/2 : ℕ))) (hs : Solvable I) :
    (2/3 : ℝ) < ((law I).iid (inputScale I^120)).probability
      (fun words => (repeated I hn hscale words).1.1 = true) := by
  simp only [repeated,DecisionRepetitionCells.value,DecisionRepetition.value]
  exact repetition_acceptance_probability (law I) _ (by unfold inputScale; omega)
    (probability I hn _ hs hden hscale)

end LowSpaceSubsetSum.WordDecisionRound

end

end OAI
