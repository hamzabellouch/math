import OAI.Combinatorics.ContingencyTables.Sampling.UnitMatrixProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTerminalProgram

namespace OAI

/-! # Deterministic terminal weights for the all-small branch -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

def terminalData (z : TerminalEntryInput) : (ProfileCheckData×ℕ)×MatrixCode :=
  ((sourceData (terminalSourceInput z),z.1.1.1.1.2),[])

def terminalDataRealizer : Realizer terminalData :=
  pair (pair (composition (f := terminalSourceInput) (g := sourceData)
    terminalSourceInputRealizer sourceDataRealizer)
    (composition (composition (composition (composition first first) first) first) second))
    (constant [])

lemma polynomial_terminalData : PolynomialTime terminalDataRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_terminalSourceInput polynomial_sourceData)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
      polynomial_second)) (polynomial_constant [])

def terminalEntry (z : TerminalEntryInput) : ℕ :=
  successfulWeight (z.2.2,(outerTrial (terminalData z),1))

def terminalEntryRealizer : Realizer terminalEntry :=
  composition (pair (composition second second)
    (pair (composition (f := terminalData) (g := outerTrial)
      terminalDataRealizer outerTrialRealizer) (constant 1))) successfulWeightRealizer

lemma polynomial_terminalEntry : PolynomialTime terminalEntryRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
    (polynomial_pair (polynomial_composition polynomial_terminalData polynomial_outerTrial)
      (polynomial_constant 1))) polynomial_successfulWeight

def terminalEntryMeasure (z : TerminalEntryInput) : ℕ := weight z

lemma work_terminalEntry : WorkBound terminalEntryRealizer terminalEntryMeasure :=
  work_of_polynomial polynomial_terminalEntry X (fun _ => by simp [terminalEntryMeasure])

abbrev TerminalColumnInput := MatrixParameters×MatrixCode
abbrev TerminalColumnEntryInput := TerminalColumnInput×(List ℕ×List ℕ)

def terminalColumnEntryInput (z : TerminalColumnEntryInput) : TerminalEntryInput :=
  (z.1.1,(z.2,z.1.2))

def terminalColumnEntryInputRealizer : Realizer terminalColumnEntryInput :=
  pair (composition first first) (pair second (composition first second))

lemma polynomial_terminalColumnEntryInput : PolynomialTime terminalColumnEntryInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair polynomial_second (polynomial_composition polynomial_first polynomial_second))

def terminalColumnEntry (z : TerminalColumnEntryInput) : ℕ := terminalEntry (terminalColumnEntryInput z)

def terminalColumnEntryRealizer : Realizer terminalColumnEntry :=
  composition (f := terminalColumnEntryInput) (g := terminalEntry)
    terminalColumnEntryInputRealizer terminalEntryRealizer

def terminalColumnEntryMeasure (z : TerminalColumnEntryInput) : ℕ :=
  terminalEntryMeasure (terminalColumnEntryInput z)+weight z

lemma work_terminalColumnEntry : WorkBound terminalColumnEntryRealizer terminalColumnEntryMeasure := by
  unfold terminalColumnEntryRealizer
  apply work_composition (work_of_polynomial polynomial_terminalColumnEntryInput X
    (fun z => by simp only [Polynomial.eval_X,terminalColumnEntryMeasure]; omega))
    work_terminalEntry X
  intro z
  simp only [Polynomial.eval_X,terminalColumnEntryMeasure]
  omega

def terminalColumn (z : TerminalColumnInput) : List ℕ :=
  (profileBoxViews (matrixData z.1)).map (fun v => terminalColumnEntry (z,v))

def terminalColumnRealizer : Realizer terminalColumn :=
  composition (f := fun z : TerminalColumnInput => (z,profileBoxViews (matrixData z.1)))
    (g := fun z : TerminalColumnInput×List (List ℕ×List ℕ) =>
      z.2.map (fun v => terminalColumnEntry (z.1,v)))
    (pair identity (composition
      (f := fun z : TerminalColumnInput => matrixData z.1) (g := profileBoxViews)
      (composition (f := fun z : TerminalColumnInput => z.1) (g := matrixData)
        first matrixDataRealizer) profileBoxViewsRealizer)) (mapWith terminalColumnEntryRealizer)

def terminalColumnMeasure (z : TerminalColumnInput) : ℕ :=
  gridStateCount (profileEnumerationData (matrixData z.1))+
    MeasuredMap.listMeasure terminalColumnEntryMeasure (z,profileBoxViews (matrixData z.1))

lemma work_terminalColumn : WorkBound terminalColumnRealizer terminalColumnMeasure := by
  have hin (z : TerminalColumnInput) : weight z ≤ terminalColumnMeasure z := by
    have hw : weight z ≤ weight (z,profileBoxViews (matrixData z.1)) :=
      weight_fst (z,profileBoxViews (matrixData z.1))
    simp only [terminalColumnMeasure,MeasuredMap.listMeasure]
    omega
  have hd : PolynomialTime (composition (first (B := MatrixCode)) matrixDataRealizer) :=
    polynomial_composition polynomial_first polynomial_matrixData
  have hv : WorkBound (composition (composition first matrixDataRealizer) profileBoxViewsRealizer)
      terminalColumnMeasure := by
    apply work_composition (work_of_polynomial hd X (fun z => by simpa using hin z))
      work_profileBoxViews (X+1)
    intro z
    have hw : weight (matrixData z.1) ≤ weight z := by
      unfold matrixData
      exact (weight_fst _).trans ((weight_fst _).trans ((weight_fst _).trans
        ((weight_fst _).trans (weight_fst z))))
    simp only [Function.comp_apply,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,
      terminalColumnMeasure,MeasuredMap.listMeasure]
    have hpair : weight z ≤ weight (z,profileBoxViews (matrixData z.1)) :=
      weight_fst (z,profileBoxViews (matrixData z.1))
    omega
  unfold terminalColumnRealizer
  apply work_composition (work_pair (work_of_polynomial polynomial_identity X
    (fun z => by simpa using hin z)) hv X (fun z => by simpa using hin z))
    (MeasuredMap.work_mapWith _ _ work_terminalColumnEntry) X
  intro z
  simp only [Polynomial.eval_X,terminalColumnMeasure,Function.comp_apply,id_eq]
  omega

end ContingencyTables.UnitCountPrograms

end OAI
