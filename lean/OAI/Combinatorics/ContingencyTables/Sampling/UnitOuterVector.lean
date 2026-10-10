import OAI.Combinatorics.ContingencyTables.Sampling.UnitOriginalVector
import OAI.Combinatorics.ContingencyTables.Sampling.OriginalTableIndex
import OAI.Combinatorics.ContingencyTables.Machines.VectorRetryProgram

namespace OAI

/-! # Computed first-success counts over the original-table box -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

/-- Walk data and margins; trial markers, denominator, and fallback matrix. -/
abbrev OuterVectorInput := TrialVectorInput×((List Bool×ℕ)×MatrixCode)

def outerVectorInput (z : OuterVectorInput) : VectorRetryPrograms.Input :=
  (z.2.1,(trialVector z.1,originalIndex (z.1.2,z.2.2)))

def outerVectorInputRealizer : Realizer outerVectorInput :=
  pair (composition second first)
    (pair (composition (f := fun z : OuterVectorInput => z.1) (g := trialVector)
      first trialVectorRealizer)
      (composition (f := fun z : OuterVectorInput => (z.1.2,z.2.2)) (g := originalIndex)
        (pair (composition first second) (composition second second)) originalIndexRealizer))

def outerVectorMeasure (z : OuterVectorInput) : ℕ := trialVectorMeasure z.1+weight z

lemma work_outerVectorInput : WorkBound outerVectorInputRealizer outerVectorMeasure := by
  have hi (z : OuterVectorInput) : weight z ≤ X.eval (outerVectorMeasure z) := by
    simp only [Polynomial.eval_X,outerVectorMeasure]
    omega
  have hv : WorkBound (composition (first (B := (List Bool×ℕ)×MatrixCode)) trialVectorRealizer)
      outerVectorMeasure := by
    apply work_composition (work_of_polynomial polynomial_first X hi) work_trialVector X
    intro z
    simp only [Polynomial.eval_X,outerVectorMeasure]
    omega
  have hp : PolynomialTime (composition
      (f := fun z : OuterVectorInput => (z.1.2,z.2.2)) (g := originalIndex)
      (pair (composition first second) (composition second second)) originalIndexRealizer) :=
    polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition polynomial_second polynomial_second)) polynomial_originalIndex
  unfold outerVectorInputRealizer
  exact work_pair (work_of_polynomial (polynomial_composition polynomial_second polynomial_first) X hi)
    (work_pair hv (work_of_polynomial hp X hi) X hi) X hi

attribute [local irreducible] outerVectorInput

def outerVector (z : OuterVectorInput) : List ℕ := VectorRetryPrograms.counts (outerVectorInput z)

def outerVectorRealizer : Realizer outerVector :=
  composition (f := outerVectorInput) (g := VectorRetryPrograms.counts)
    outerVectorInputRealizer VectorRetryPrograms.countsRealizer

lemma work_outerVector : WorkBound outerVectorRealizer outerVectorMeasure := by
  unfold outerVectorRealizer
  exact work_then_polynomial work_outerVectorInput VectorRetryPrograms.polynomial_counts

end ContingencyTables.UnitCountPrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms UnitCountPrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts OriginalTableBox
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (b h : ℕ) (hsmall : ∀ i j,paperSmall r c i j=true)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

attribute [local irreducible] UnitCountPrograms.trialVector unitTrialCounts matrixInput UnitCountPrograms.outerVectorInput

lemma unit_outerVector_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (N : ℕ) (js : List Bool) (fallback : Table r c) :
    UnitCountPrograms.outerVector (((matrixInput r c e b h z xs,(N,(profileIndex r c e z).val)),
      (List.ofFn r,List.ofFn c)),((js,(2^s)^N),matrixCode fallback.val))=
      List.ofFn ((OriginalBoxLaw.law r c le_rfl
        (unitTrialCounts r c e hsmall z N)).retry
        (OriginalTableBox.index r c le_rfl fallback) js.length).count := by
  unfold UnitCountPrograms.outerVector UnitCountPrograms.outerVectorInput
  rw [unit_trialVector_actual r c e b h hsmall htotal z xs hs N,originalIndex_actual]
  exact VectorRetryPrograms.counts_actual _ js _

end
end ContingencyTables.SmallGraphProfiles

end OAI
