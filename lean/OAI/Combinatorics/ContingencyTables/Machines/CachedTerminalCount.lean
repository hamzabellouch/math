import OAI.Combinatorics.ContingencyTables.Machines.PreparedTransitionCache
import OAI.Combinatorics.ContingencyTables.Machines.MatrixCodeEquality
import OAI.Combinatorics.ContingencyTables.Sampling.OuterTrialProgram

namespace OAI

/-! # Exact terminal counts from the retained dense-completion cache -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev TerminalOutputInput := (ProfileCheckData×ℕ)×(Option MatrixCode×ℕ)

def terminalOutputEntry (z : TerminalOutputInput) : Option MatrixCode×ℕ :=
  (z.2.1.bind (fun X => outerTrial (z.1,X)),z.2.2)

def terminalOutputEntryRealizer : Realizer terminalOutputEntry :=
  (pair (composition (pair first (composition second first))
    (optionCases (constant none) outerTrialRealizer)) (composition second second)).congr (by
      rintro ⟨p,⟨o,n⟩⟩
      cases o <;> rfl)

lemma polynomial_terminalOutputEntry : PolynomialTime terminalOutputEntryRealizer := by
  unfold terminalOutputEntryRealizer
  apply polynomial_congr
  exact polynomial_pair (polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_first))
    (polynomial_optionCases (polynomial_constant none) polynomial_outerTrial))
    (polynomial_composition polynomial_second polynomial_second)

def terminalOutputs (z : TransitionCache) : List (Option MatrixCode×ℕ) :=
  z.2.2.map (fun entry => terminalOutputEntry (z.1.1,entry))

def terminalOutputsRealizer : Realizer terminalOutputs :=
  composition (pair (composition first first) (composition second second))
    (mapWith terminalOutputEntryRealizer)

lemma polynomial_terminalOutputs : PolynomialTime terminalOutputsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition polynomial_second polynomial_second))
    (polynomial_mapWith polynomial_terminalOutputEntry)

def successfulWeight (z : MatrixCode×(Option MatrixCode×ℕ)) : ℕ :=
  z.2.1.elim 0 (fun X => if X=z.1 then z.2.2 else 0)

def successfulWeightRealizer : Realizer successfulWeight := by
  let input : Realizer (fun z : MatrixCode×(Option MatrixCode×ℕ) =>
      ((z.1,z.2.2),z.2.1)) := pair (pair first (composition second second))
    (composition second first)
  let test : Realizer (fun z : (MatrixCode×ℕ)×MatrixCode => decide (z.2=z.1.1)) :=
    composition (pair second (composition first first)) matrixEqual
  let result := choose test (composition first second) (constant 0)
  exact (composition input (optionCases (constant 0) result)).congr (by
    intro z
    simp only [Function.comp_apply,decide_eq_true_eq]
    rfl)

lemma polynomial_successfulWeight : PolynomialTime successfulWeightRealizer := by
  unfold successfulWeightRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_second))
    (polynomial_composition polynomial_second polynomial_first))
    (polynomial_optionCases (polynomial_constant 0) (polynomial_choose
      (polynomial_composition (polynomial_pair polynomial_second
        (polynomial_composition polynomial_first polynomial_first)) polynomial_matrixEqual)
      (polynomial_composition polynomial_first polynomial_second) (polynomial_constant 0)))

def successfulWeightSum (z : MatrixCode×List (Option MatrixCode×ℕ)) : ℕ :=
  (z.2.map (fun entry => successfulWeight (z.1,entry))).sum

def successfulWeightSumRealizer : Realizer successfulWeightSum :=
  composition (mapWith successfulWeightRealizer) listSum

lemma polynomial_successfulWeightSum : PolynomialTime successfulWeightSumRealizer :=
  polynomial_composition (polynomial_mapWith polynomial_successfulWeight) polynomial_listSum

def terminalCount (z : TransitionCache×MatrixCode) : ℕ :=
  z.1.2.1*successfulWeightSum (z.2,terminalOutputs z.1)

def terminalCountRealizer : Realizer terminalCount :=
  composition (pair (composition (composition first second) first)
    (composition (pair second (composition first terminalOutputsRealizer))
      successfulWeightSumRealizer)) multiply

lemma polynomial_terminalCount : PolynomialTime terminalCountRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_terminalOutputs)) polynomial_successfulWeightSum))
    polynomial_multiply

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.ProfilePrograms
open DensePrograms

lemma terminalCount_eq (p : ResidualParameters) (M : ℕ)
    (entries : List (Option MatrixCode×ℕ)) (target : MatrixCode) :
    terminalCount ((p,(M,entries)),target)=
      M*(entries.map (fun entry => entry.1.elim 0
        (fun X => if outerTrial (p.1,X)=some target then entry.2 else 0))).sum := by
  unfold terminalCount terminalOutputs successfulWeightSum
  rw [List.map_map]
  congr 2
  apply List.map_congr_left
  rintro ⟨o,n⟩ _
  cases o with
  | none => rfl
  | some X =>
    simp only [Function.comp_apply,terminalOutputEntry,Option.bind_some,successfulWeight,
      Option.elim_some]
    cases outerTrial (p.1,X) with
    | none => rfl
    | some Y => simp only [Option.elim_some,Option.some.injEq]

end ContingencyTables.ProfilePrograms

end OAI
