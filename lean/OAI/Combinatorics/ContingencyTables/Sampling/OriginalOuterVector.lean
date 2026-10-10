import OAI.Combinatorics.ContingencyTables.Sampling.OriginalTrialVector
import OAI.Combinatorics.ContingencyTables.Sampling.OriginalTableIndex
import OAI.Combinatorics.ContingencyTables.Machines.VectorRetryProgram

namespace OAI

/-! # Computed first-success counts over the original-table box -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

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

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts OriginalTableBox
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

attribute [local irreducible] trialVector listedTrialCounts matrixInput outerVectorInput

lemma outerVector_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (N : ℕ) (js : List Bool) (fallback : Table r c) :
    outerVector (((matrixInput r c e b h z xs,(N,(profileIndex r c e z).val)),
      (List.ofFn r,List.ofFn c)),((js,(2^(s+f))^N*2^f),matrixCode fallback.val))=
      List.ofFn ((OriginalBoxLaw.law r c le_rfl
        (listedTrialCounts r c e hr hc b h hb z N)).retry
        (OriginalTableBox.index r c le_rfl fallback) js.length).count := by
  unfold outerVector outerVectorInput
  rw [trialVector_actual r c e hr hc b h hb htotal z xs hs N,originalIndex_actual]
  exact VectorRetryPrograms.counts_actual _ js _

end
end ContingencyTables.SmallGraphProfiles

end OAI
