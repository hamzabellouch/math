import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoNormSubstitutionError

namespace OAI

section

noncomputable section
namespace InternalCatalan

def manuscriptNormPRoundedSubstituteRat : ℚ :=
  manuscriptNormPRoundedSubstituteRow0 +
    manuscriptNormPRoundedSubstituteRow1 +
    manuscriptNormPRoundedSubstituteRow2 +
    manuscriptNormPRoundedSubstituteRow3 +
    manuscriptNormPRoundedSubstituteRow4 +
    manuscriptNormPRoundedSubstituteRow5 +
    manuscriptNormPRoundedSubstituteRow6 +
    manuscriptNormPRoundedSubstituteRow7 +
    manuscriptNormPRoundedSubstituteRow8 +
    manuscriptNormPRoundedSubstituteRow9

theorem manuscriptNormPRoundedSubstitute_error :
    |(manuscriptNormPSubstituteRat : ℝ) - (manuscriptNormPRoundedSubstituteRat : ℝ)| ≤
      (((7534102673602743 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormPRoundedRow0_error
  have h1 := manuscriptNormPRoundedRow1_error
  have h2 := manuscriptNormPRoundedRow2_error
  have h3 := manuscriptNormPRoundedRow3_error
  have h4 := manuscriptNormPRoundedRow4_error
  have h5 := manuscriptNormPRoundedRow5_error
  have h6 := manuscriptNormPRoundedRow6_error
  have h7 := manuscriptNormPRoundedRow7_error
  have h8 := manuscriptNormPRoundedRow8_error
  have h9 := manuscriptNormPRoundedRow9_error
  unfold manuscriptNormPSubstituteRat manuscriptNormPRoundedSubstituteRat
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢
  apply abs_le.mpr
  constructor
  · linarith only [(abs_le.mp h0).1,
    (abs_le.mp h1).1,
    (abs_le.mp h2).1,
    (abs_le.mp h3).1,
    (abs_le.mp h4).1,
    (abs_le.mp h5).1,
    (abs_le.mp h6).1,
    (abs_le.mp h7).1,
    (abs_le.mp h8).1,
    (abs_le.mp h9).1]
  · linarith only [(abs_le.mp h0).2,
    (abs_le.mp h1).2,
    (abs_le.mp h2).2,
    (abs_le.mp h3).2,
    (abs_le.mp h4).2,
    (abs_le.mp h5).2,
    (abs_le.mp h6).2,
    (abs_le.mp h7).2,
    (abs_le.mp h8).2,
    (abs_le.mp h9).2]

def manuscriptNormVRoundedSubstituteRat : ℚ :=
  manuscriptNormVRoundedSubstituteRow0 +
    manuscriptNormVRoundedSubstituteRow1 +
    manuscriptNormVRoundedSubstituteRow2 +
    manuscriptNormVRoundedSubstituteRow3 +
    manuscriptNormVRoundedSubstituteRow4 +
    manuscriptNormVRoundedSubstituteRow5 +
    manuscriptNormVRoundedSubstituteRow6 +
    manuscriptNormVRoundedSubstituteRow7 +
    manuscriptNormVRoundedSubstituteRow8 +
    manuscriptNormVRoundedSubstituteRow9 +
    manuscriptNormVRoundedSubstituteRow10 +
    manuscriptNormVRoundedSubstituteRow11 +
    manuscriptNormVRoundedSubstituteRow12

theorem manuscriptNormVRoundedSubstitute_error :
    |(manuscriptNormVSubstituteRat : ℝ) - (manuscriptNormVRoundedSubstituteRat : ℝ)| ≤
      (((16965587287251693 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormVRoundedRow0_error
  have h1 := manuscriptNormVRoundedRow1_error
  have h2 := manuscriptNormVRoundedRow2_error
  have h3 := manuscriptNormVRoundedRow3_error
  have h4 := manuscriptNormVRoundedRow4_error
  have h5 := manuscriptNormVRoundedRow5_error
  have h6 := manuscriptNormVRoundedRow6_error
  have h7 := manuscriptNormVRoundedRow7_error
  have h8 := manuscriptNormVRoundedRow8_error
  have h9 := manuscriptNormVRoundedRow9_error
  have h10 := manuscriptNormVRoundedRow10_error
  have h11 := manuscriptNormVRoundedRow11_error
  have h12 := manuscriptNormVRoundedRow12_error
  unfold manuscriptNormVSubstituteRat manuscriptNormVRoundedSubstituteRat
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 ⊢
  apply abs_le.mpr
  constructor
  · linarith only [(abs_le.mp h0).1,
    (abs_le.mp h1).1,
    (abs_le.mp h2).1,
    (abs_le.mp h3).1,
    (abs_le.mp h4).1,
    (abs_le.mp h5).1,
    (abs_le.mp h6).1,
    (abs_le.mp h7).1,
    (abs_le.mp h8).1,
    (abs_le.mp h9).1,
    (abs_le.mp h10).1,
    (abs_le.mp h11).1,
    (abs_le.mp h12).1]
  · linarith only [(abs_le.mp h0).2,
    (abs_le.mp h1).2,
    (abs_le.mp h2).2,
    (abs_le.mp h3).2,
    (abs_le.mp h4).2,
    (abs_le.mp h5).2,
    (abs_le.mp h6).2,
    (abs_le.mp h7).2,
    (abs_le.mp h8).2,
    (abs_le.mp h9).2,
    (abs_le.mp h10).2,
    (abs_le.mp h11).2,
    (abs_le.mp h12).2]

def manuscriptCase2NormRoundedSubstituteRat : ℚ :=
  2 * (manuscriptRatFiniteCross barrierP2Finite manuscriptP2RatTail +
    manuscriptNormPRoundedSubstituteRat) +
  (1 / 2 : ℚ) * (manuscriptRatFiniteCross barrierV2Finite manuscriptV2RatTail +
    manuscriptNormVRoundedSubstituteRat)

theorem manuscript_case2_norm_added_rounding_error_le :
    |(manuscriptCase2NormSubstituteRat : ℝ) -
      (manuscriptCase2NormRoundedSubstituteRat : ℝ)| ≤
      (((9420399596332533 / 2000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have hP := manuscriptNormPRoundedSubstitute_error
  have hV := manuscriptNormVRoundedSubstitute_error
  unfold manuscriptCase2NormSubstituteRat manuscriptCase2NormRoundedSubstituteRat
  push_cast at hP hV ⊢
  apply abs_le.mpr
  constructor
  · linarith only [(abs_le.mp hP).1, (abs_le.mp hV).1]
  · linarith only [(abs_le.mp hP).2, (abs_le.mp hV).2]

theorem manuscript_case2_norm_added_rounding_error :
    |(manuscriptCase2NormSubstituteRat : ℝ) -
      (manuscriptCase2NormRoundedSubstituteRat : ℝ)| < (1 / (10 : ℝ) ^ 32) := by
  apply manuscript_case2_norm_added_rounding_error_le.trans_lt
  norm_num [manuscriptTermRoundStep]

end InternalCatalan

end

end

end OAI
