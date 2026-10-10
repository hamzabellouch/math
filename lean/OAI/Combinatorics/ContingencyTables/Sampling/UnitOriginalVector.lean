import OAI.Combinatorics.ContingencyTables.Sampling.UnitTerminalSemantics
import OAI.Combinatorics.ContingencyTables.Sampling.OriginalBoxLaw

namespace OAI

/-! # Computing trial counts on every original-table candidate -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

abbrev OptionalTrialInput := WalkCountInput×Option MatrixCode

def optionalTrialInput (z : OptionalTrialInput) : TrialCountInput := (z.1,z.2.getD [])

def optionalTrialInputRealizer : Realizer optionalTrialInput :=
  pair first (composition (pair (constant ([] : MatrixCode)) second) FirstSuccessProgram.defaultRealizer)

lemma polynomial_optionalTrialInput : PolynomialTime optionalTrialInputRealizer :=
  polynomial_pair polynomial_first (polynomial_composition
    (polynomial_pair (polynomial_constant []) polynomial_second) FirstSuccessProgram.polynomial_default)

def optionalTrialCount (z : OptionalTrialInput) : ℕ :=
  if z.2.isSome then trialCount (optionalTrialInput z) else 0

def optionalTrialCountRealizer : Realizer optionalTrialCount :=
  choose (composition second FirstSuccessProgram.isSomeRealizer)
    (composition (f := optionalTrialInput) (g := trialCount)
      optionalTrialInputRealizer trialCountRealizer) (constant 0)

def optionalTrialMeasure (z : OptionalTrialInput) : ℕ :=
  trialCountMeasure (optionalTrialInput z)+weight z

lemma work_optionalTrialCount : WorkBound optionalTrialCountRealizer optionalTrialMeasure := by
  have hi (z : OptionalTrialInput) : weight z ≤ X.eval (optionalTrialMeasure z) := by
    simp only [Polynomial.eval_X,optionalTrialMeasure]
    omega
  have ht : WorkBound (composition optionalTrialInputRealizer trialCountRealizer)
      optionalTrialMeasure := by
    apply work_composition (work_of_polynomial polynomial_optionalTrialInput X hi) work_trialCount X
    intro z
    simp only [Polynomial.eval_X,optionalTrialMeasure]
    omega
  unfold optionalTrialCountRealizer
  exact work_choose (work_of_polynomial (polynomial_composition polynomial_second
    FirstSuccessProgram.polynomial_isSome) X hi) ht
    (work_of_polynomial (polynomial_constant 0) X hi) X hi

abbrev TrialVectorInput := WalkCountInput×CompletionMargins

def trialVector (z : TrialVectorInput) : List ℕ :=
  (originalCandidates z.2).map (fun o => optionalTrialCount (z.1,o))

def trialVectorRealizer : Realizer trialVector :=
  composition (f := fun z : TrialVectorInput => (z.1,originalCandidates z.2))
    (g := fun z : WalkCountInput×List (Option MatrixCode) =>
      z.2.map (fun o => optionalTrialCount (z.1,o)))
    (pair first (composition second originalCandidatesRealizer))
    (mapWith optionalTrialCountRealizer)

def trialVectorMeasure (z : TrialVectorInput) : ℕ :=
  originalEnumerationMeasure z.2+
    MeasuredMap.listMeasure optionalTrialMeasure (z.1,originalCandidates z.2)+weight z

lemma work_trialVector : WorkBound trialVectorRealizer trialVectorMeasure := by
  have hi (z : TrialVectorInput) : weight z ≤ X.eval (trialVectorMeasure z) := by
    simp only [Polynomial.eval_X,trialVectorMeasure]
    omega
  have he : WorkBound (composition (second (A := WalkCountInput)) originalCandidatesRealizer)
      trialVectorMeasure := by
    apply work_composition (work_of_polynomial polynomial_second X hi) work_originalCandidates X
    intro z
    simp only [Polynomial.eval_X,trialVectorMeasure]
    omega
  unfold trialVectorRealizer
  apply work_composition (work_pair (work_of_polynomial polynomial_first X hi) he X hi)
    (MeasuredMap.work_mapWith _ _ work_optionalTrialCount) X
  intro z
  simp only [Polynomial.eval_X,trialVectorMeasure,Function.comp_apply]
  omega

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

attribute [local irreducible] UnitCountPrograms.trialCount unitTrialCounts matrixInput

lemma unit_trialVector_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (N : ℕ) :
    UnitCountPrograms.trialVector ((matrixInput r c e b h z xs,(N,(profileIndex r c e z).val)),
      (List.ofFn r,List.ofFn c))=
      List.ofFn (fun k : OriginalTableBox.Index m n (∑ i,r i) =>
        (OriginalBoxLaw.law r c le_rfl (unitTrialCounts r c e hsmall z N)).count (some k)) := by
  unfold UnitCountPrograms.trialVector
  rw [candidates_code,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  rw [OriginalBoxLaw.count_some]
  dsimp only [Function.comp_apply]
  cases he : tableAt r c k with
  | none => rfl
  | some T =>
    simp only [Option.map_some,UnitCountPrograms.optionalTrialCount,Option.isSome_some,ite_true,UnitCountPrograms.optionalTrialInput,
      Option.getD_some,Option.elim_some]
    exact unit_trialCount_actual r c e b h htotal hsmall z xs hs N T

end
end ContingencyTables.SmallGraphProfiles

end OAI
