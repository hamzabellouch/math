import OAI.Combinatorics.ContingencyTables.Sampling.UnitTerminalProgram
import OAI.Combinatorics.ContingencyTables.Transport.IntegerMatrixPoint

namespace OAI

/-! # Executed walk-and-terminal integer trial counts -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

abbrev WalkCountInput := MatrixParameters×(ℕ×ℕ)

def walkCountData (z : WalkCountInput) : ℕ×(List (List ℕ)×ℕ) :=
  (z.2.1,(profileMatrix z.1,z.2.2))

def walkCountDataRealizer : Realizer walkCountData :=
  pair (composition second first)
    (pair (composition (f := fun z : WalkCountInput => z.1) (g := profileMatrix)
      first profileMatrixRealizer) (composition second second))

def walkCountMeasure (z : WalkCountInput) : ℕ :=
  z.2.1+profileMatrixMeasure z.1+weight z

lemma work_walkCountData : WorkBound walkCountDataRealizer walkCountMeasure := by
  have hi (z : WalkCountInput) : weight z ≤ X.eval (walkCountMeasure z) := by
    simp only [Polynomial.eval_X,walkCountMeasure]
    omega
  have hm : WorkBound (composition (first (B := ℕ×ℕ)) profileMatrixRealizer) walkCountMeasure := by
    apply work_composition (work_of_polynomial polynomial_first X hi) work_profileMatrix X
    intro z
    simp only [Polynomial.eval_X,walkCountMeasure]
    omega
  unfold walkCountDataRealizer
  exact work_pair (work_of_polynomial (polynomial_composition polynomial_second polynomial_first) X hi)
    (work_pair hm (work_of_polynomial
      (polynomial_composition polynomial_second polynomial_second) X hi) X hi) X hi

def walkCounts (z : WalkCountInput) : List ℕ := IntegerMatrixPrograms.fromPoint (walkCountData z)

def walkCountsRealizer : Realizer walkCounts :=
  composition (f := walkCountData) (g := IntegerMatrixPrograms.fromPoint)
    walkCountDataRealizer IntegerMatrixPrograms.fromPointRealizer

lemma work_walkCounts : WorkBound walkCountsRealizer walkCountMeasure := by
  obtain ⟨p,hp⟩ := work_walkCountData
  unfold walkCountsRealizer
  apply work_composition ⟨p,hp⟩ IntegerMatrixPrograms.work_fromPoint (X+p)
  intro z
  have hw := hp z
  have hs : weight (profileMatrix z.1,z.2.2) ≤ weight (walkCountData z) := by
    exact weight_snd (walkCountData z)
  have hn : z.2.1 ≤ walkCountMeasure z := by unfold walkCountMeasure; omega
  simp only [Polynomial.eval_add,Polynomial.eval_X]
  change z.2.1+weight (profileMatrix z.1,z.2.2) ≤ _
  omega

abbrev TrialCountInput := WalkCountInput×MatrixCode

def trialCount (z : TrialCountInput) : ℕ :=
  IntegerMatrixPrograms.dot (walkCounts z.1,terminalColumn (z.1.1,z.2))

def trialCountRealizer : Realizer trialCount :=
  composition (pair (composition (f := fun z : TrialCountInput => z.1) (g := walkCounts)
      first walkCountsRealizer)
    (composition (f := fun z : TrialCountInput => (z.1.1,z.2)) (g := terminalColumn)
      (pair (composition first first) second) terminalColumnRealizer)) IntegerMatrixPrograms.dotRealizer

def trialCountMeasure (z : TrialCountInput) : ℕ :=
  walkCountMeasure z.1+terminalColumnMeasure (z.1.1,z.2)+weight z

lemma work_trialCount : WorkBound trialCountRealizer trialCountMeasure := by
  have hi (z : TrialCountInput) : weight z ≤ X.eval (trialCountMeasure z) := by
    simp only [Polynomial.eval_X,trialCountMeasure]
    omega
  have hw : WorkBound (composition (first (B := MatrixCode)) walkCountsRealizer) trialCountMeasure := by
    apply work_composition (work_of_polynomial polynomial_first X hi) work_walkCounts X
    intro z
    simp only [Polynomial.eval_X,trialCountMeasure]
    omega
  have ht : WorkBound (composition (pair (composition first first) second)
      terminalColumnRealizer) trialCountMeasure := by
    apply work_composition (work_of_polynomial (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) X hi)
      work_terminalColumn X
    intro z
    simp only [Polynomial.eval_X,trialCountMeasure,Function.comp_apply]
    omega
  unfold trialCountRealizer
  exact work_then_polynomial (work_pair hw ht X hi) IntegerMatrixPrograms.polynomial_dot

end ContingencyTables.UnitCountPrograms

end OAI
