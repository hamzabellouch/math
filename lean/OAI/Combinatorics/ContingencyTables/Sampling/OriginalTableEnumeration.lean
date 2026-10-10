import OAI.Combinatorics.ContingencyTables.Sampling.OriginalTableCheck
import OAI.Combinatorics.ContingencyTables.Machines.CompletionEnumerationProgram

namespace OAI

/-! # Enumerating original tables by all their bounded entries -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

/-- Dummy leading margins reuse the rectangular free-array layout only. -/
def originalLayoutMargins (z : CompletionMargins) : CompletionMargins := (0::z.1,0::z.2)

def originalLayoutMarginsRealizer : Realizer originalLayoutMargins :=
  pair (composition (f := fun z : CompletionMargins => (0,z.1))
      (g := fun z : ℕ×List ℕ => z.1::z.2) (pair (constant 0) first) listCons)
    (composition (f := fun z : CompletionMargins => (0,z.2))
      (g := fun z : ℕ×List ℕ => z.1::z.2) (pair (constant 0) second) listCons)

lemma polynomial_originalLayoutMargins : PolynomialTime originalLayoutMarginsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_constant 0) polynomial_first) polynomial_listCons)
    (polynomial_composition (polynomial_pair (polynomial_constant 0) polynomial_second) polynomial_listCons)

def originalFreeMatrix (z : CompletionMargins×List ℕ) : MatrixCode :=
  unflattenGrid (originalLayoutMargins z.1,z.2)

def originalFreeMatrixRealizer : Realizer originalFreeMatrix :=
  composition (pair (composition first originalLayoutMarginsRealizer) second) unflattenGridRealizer

lemma polynomial_originalFreeMatrix : PolynomialTime originalFreeMatrixRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_originalLayoutMargins) polynomial_second)
    polynomial_unflattenGrid

def originalCandidate (z : CompletionMargins×List ℕ) : Option MatrixCode :=
  let X := originalFreeMatrix z
  if originalTableTest (z.1,X) then some X else none

def originalCandidateRealizer : Realizer originalCandidate :=
  choose (composition (pair first originalFreeMatrixRealizer) originalTableTestRealizer)
    (composition originalFreeMatrixRealizer some) (constant none)

lemma polynomial_originalCandidate : PolynomialTime originalCandidateRealizer :=
  polynomial_choose (polynomial_composition
    (polynomial_pair polynomial_first polynomial_originalFreeMatrix) polynomial_originalTableTest)
    (polynomial_composition polynomial_originalFreeMatrix polynomial_some) (polynomial_constant none)

def originalEnumerationData (z : CompletionMargins) : GridEnumerationData :=
  completionEnumerationData (originalLayoutMargins z)

def originalEnumerationDataRealizer : Realizer originalEnumerationData :=
  composition originalLayoutMarginsRealizer completionEnumerationDataRealizer

lemma polynomial_originalEnumerationData : PolynomialTime originalEnumerationDataRealizer :=
  polynomial_composition polynomial_originalLayoutMargins polynomial_completionEnumerationData

def originalCandidates (z : CompletionMargins) : List (Option MatrixCode) :=
  (gridWords (originalEnumerationData z)).map (fun v => originalCandidate (z,v))

def originalCandidatesRealizer : Realizer originalCandidates :=
  composition (pair identity (composition originalEnumerationDataRealizer gridWordsRealizer))
    (mapWith originalCandidateRealizer)

def originalEnumerationMeasure (z : CompletionMargins) : ℕ :=
  gridStateCount (originalEnumerationData z)+weight z

lemma work_originalCandidates : WorkBound originalCandidatesRealizer originalEnumerationMeasure := by
  have hp : WorkBound originalEnumerationDataRealizer originalEnumerationMeasure :=
    work_of_polynomial polynomial_originalEnumerationData X
      (fun z => by simp only [Polynomial.eval_X,originalEnumerationMeasure]; omega)
  obtain ⟨p,hp'⟩ := hp
  have hg : WorkBound (composition originalEnumerationDataRealizer gridWordsRealizer)
      originalEnumerationMeasure := by
    apply work_composition ⟨p,hp'⟩ work_gridWords (X+p)
    intro z
    have hw := hp' z
    simp only [Polynomial.eval_add,Polynomial.eval_X]
    change gridStateCount (originalEnumerationData z)+weight (originalEnumerationData z) ≤ _
    unfold originalEnumerationMeasure at hw ⊢
    omega
  unfold originalCandidatesRealizer
  apply work_then_polynomial _ (polynomial_mapWith polynomial_originalCandidate)
  exact work_pair (work_of_polynomial polynomial_identity X
    (fun z => by simp only [Polynomial.eval_X,originalEnumerationMeasure]; omega)) hg X
    (fun z => by simp only [Polynomial.eval_X,originalEnumerationMeasure]; omega)

end ContingencyTables.ProfilePrograms

end OAI
