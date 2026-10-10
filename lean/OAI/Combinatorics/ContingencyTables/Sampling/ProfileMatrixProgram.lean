import OAI.Combinatorics.ContingencyTables.Sampling.ProfileMatrixEntryRuntime
import OAI.Combinatorics.ContingencyTables.Transport.MeasuredMap

namespace OAI

/-! # Constructing the finite transition matrix by deterministic enumeration -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

abbrev MatrixColumnInput := MatrixParameters×(List ℕ×List ℕ)
abbrev MatrixColumnEntryInput := MatrixColumnInput×(List ℕ×List ℕ)

def columnEntryInput (z : MatrixColumnEntryInput) : MatrixEntryInput :=
  (z.1.1,(z.2,z.1.2))

def columnEntryInputRealizer : Realizer columnEntryInput :=
  pair (composition first first) (pair second (composition first second))

lemma polynomial_columnEntryInput : PolynomialTime columnEntryInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair polynomial_second (polynomial_composition polynomial_first polynomial_second))

def columnEntry (z : MatrixColumnEntryInput) : ℕ := matrixEntry (columnEntryInput z)

def columnEntryRealizer : Realizer columnEntry :=
  composition (f := columnEntryInput) (g := matrixEntry) columnEntryInputRealizer matrixEntryRealizer

def columnEntryMeasure (z : MatrixColumnEntryInput) : ℕ :=
  matrixEntryMeasure (columnEntryInput z)

lemma work_columnEntry : WorkBound columnEntryRealizer columnEntryMeasure := by
  unfold columnEntryRealizer
  apply work_composition (work_of_polynomial polynomial_columnEntryInput X _) work_matrixEntry X
  · intro z
    simp only [columnEntryMeasure,Polynomial.eval_X]
    exact le_rfl
  · intro z
    have hz : weight z=weight (columnEntryInput z) := by
      rcases z with ⟨⟨p,t⟩,s⟩
      simp only [columnEntryInput,weight_prod]
      omega
    simp only [Polynomial.eval_X,columnEntryMeasure,matrixEntryMeasure]
    omega

def matrixColumn (z : MatrixColumnInput) : List ℕ :=
  (profileBoxViews (matrixData z.1)).map (fun source => columnEntry (z,source))

def matrixColumnRealizer : Realizer matrixColumn :=
  composition (f := fun z : MatrixColumnInput => (z,profileBoxViews (matrixData z.1)))
    (g := fun z : MatrixColumnInput×List (List ℕ×List ℕ) =>
      z.2.map (fun source => columnEntry (z.1,source)))
    (pair identity (composition
      (f := fun z : MatrixColumnInput => matrixData z.1) (g := profileBoxViews)
      (composition (f := fun z : MatrixColumnInput => z.1) (g := matrixData)
        first matrixDataRealizer) profileBoxViewsRealizer)) (mapWith columnEntryRealizer)

def matrixColumnMeasure (z : MatrixColumnInput) : ℕ :=
  gridStateCount (profileEnumerationData (matrixData z.1))+
    MeasuredMap.listMeasure columnEntryMeasure (z,profileBoxViews (matrixData z.1))

lemma work_matrixColumn : WorkBound matrixColumnRealizer matrixColumnMeasure := by
  have hin (z : MatrixColumnInput) : weight z ≤ matrixColumnMeasure z := by
    have hw : weight z ≤ weight (z,profileBoxViews (matrixData z.1)) := weight_fst (z,profileBoxViews (matrixData z.1))
    simp only [matrixColumnMeasure,MeasuredMap.listMeasure]
    omega
  have hd : PolynomialTime (composition (first (B := List ℕ×List ℕ)) matrixDataRealizer) :=
    polynomial_composition polynomial_first polynomial_matrixData
  have hv : WorkBound (composition (composition first matrixDataRealizer) profileBoxViewsRealizer)
      matrixColumnMeasure := by
    apply work_composition (work_of_polynomial hd X (fun z => by simpa using hin z))
      work_profileBoxViews (X+1)
    intro z
    have hw : weight (matrixData z.1) ≤ weight z := by
      unfold matrixData
      exact (weight_fst _).trans ((weight_fst _).trans ((weight_fst _).trans
        ((weight_fst _).trans (weight_fst z))))
    simp only [Function.comp_apply,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,
      matrixColumnMeasure,MeasuredMap.listMeasure]
    have hpair : weight z ≤ weight (z,profileBoxViews (matrixData z.1)) := weight_fst (z,profileBoxViews (matrixData z.1))
    omega
  unfold matrixColumnRealizer
  apply work_composition (work_pair (work_of_polynomial polynomial_identity X
    (fun z => by simpa using hin z)) hv X (fun z => by simpa using hin z))
    (MeasuredMap.work_mapWith _ _ work_columnEntry) X
  intro z
  simp only [Polynomial.eval_X,matrixColumnMeasure,Function.comp_apply,id_eq]
  omega

def profileMatrix (z : MatrixParameters) : List (List ℕ) :=
  (profileBoxViews (matrixData z)).map (fun target => matrixColumn (z,target))

def profileMatrixRealizer : Realizer profileMatrix :=
  composition (f := fun z : MatrixParameters => (z,profileBoxViews (matrixData z)))
    (g := fun z : MatrixParameters×List (List ℕ×List ℕ) =>
      z.2.map (fun target => matrixColumn (z.1,target)))
    (pair identity (composition (f := matrixData) (g := profileBoxViews)
      matrixDataRealizer profileBoxViewsRealizer)) (mapWith matrixColumnRealizer)

def profileMatrixMeasure (z : MatrixParameters) : ℕ :=
  gridStateCount (profileEnumerationData (matrixData z))+
    MeasuredMap.listMeasure matrixColumnMeasure (z,profileBoxViews (matrixData z))

lemma work_profileMatrix : WorkBound profileMatrixRealizer profileMatrixMeasure := by
  have hin (z : MatrixParameters) : weight z ≤ profileMatrixMeasure z := by
    have hw : weight z ≤ weight (z,profileBoxViews (matrixData z)) := weight_fst (z,profileBoxViews (matrixData z))
    simp only [profileMatrixMeasure,MeasuredMap.listMeasure]
    omega
  have hv : WorkBound (composition matrixDataRealizer profileBoxViewsRealizer)
      profileMatrixMeasure := by
    apply work_composition (work_of_polynomial polynomial_matrixData X
      (fun z => by simpa using hin z)) work_profileBoxViews (X+1)
    intro z
    have hw : weight (matrixData z) ≤ weight z := by
      unfold matrixData
      exact (weight_fst _).trans ((weight_fst _).trans ((weight_fst _).trans (weight_fst z)))
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,
      profileMatrixMeasure,MeasuredMap.listMeasure]
    have hpair : weight z ≤ weight (z,profileBoxViews (matrixData z)) := weight_fst (z,profileBoxViews (matrixData z))
    omega
  unfold profileMatrixRealizer
  apply work_composition (work_pair (work_of_polynomial polynomial_identity X
    (fun z => by simpa using hin z)) hv X (fun z => by simpa using hin z))
    (MeasuredMap.work_mapWith _ _ work_matrixColumn) X
  intro z
  simp only [Polynomial.eval_X,profileMatrixMeasure,Function.comp_apply,id_eq]
  omega

end ContingencyTables.ProfilePrograms

end OAI
