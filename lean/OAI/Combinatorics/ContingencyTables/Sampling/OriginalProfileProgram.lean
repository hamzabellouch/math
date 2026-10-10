import OAI.Combinatorics.ContingencyTables.Sampling.OriginalProfileEntries
import OAI.Combinatorics.ContingencyTables.Sampling.GreedyPublicProgram
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperPreparedProposal
import OAI.Combinatorics.ContingencyTables.Dense.DenseIntegerProgram

namespace OAI

/-! # Computing the initial profile directly from the greedy table -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

abbrev OriginalViewInput := (List (ℕ×ℕ)×ℕ)×MatrixCode

def originalFirstView (z : OriginalViewInput) : List ℕ :=
  z.1.1.map (fun ij => matrixEntry (z.2,ij))
def originalFirstViewRealizer : Realizer originalFirstView :=
  composition (pair second (composition first first)) (mapWith matrixEntryRealizer)

theorem polynomial_originalFirstView : PolynomialTime originalFirstViewRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_first polynomial_first)) (polynomial_mapWith polynomial_matrixEntry)

def originalViews (z : OriginalViewInput) : List ℕ×List ℕ :=
  (originalFirstView z,complementValues (z.1.2,originalFirstView z))
def originalViewsRealizer : Realizer originalViews :=
  pair originalFirstViewRealizer
    (composition (pair (composition first second) originalFirstViewRealizer) complementValuesRealizer)

theorem polynomial_originalViews : PolynomialTime originalViewsRealizer :=
  polynomial_pair polynomial_originalFirstView
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
      polynomial_originalFirstView) polynomial_complementValues)

def initialViewInput (z : List ℕ×List ℕ) : OriginalViewInput :=
  ((marginCatalog z,marginThreshold z),GreedyFeasibleTable.listMatrix z.1 z.2)
def initialViewInputRealizer : Realizer initialViewInput :=
  pair (pair marginCatalogRealizer marginThresholdRealizer) GreedyFeasibleTable.tableRealizer

theorem polynomial_initialViewInput : PolynomialTime initialViewInputRealizer :=
  polynomial_pair (polynomial_pair polynomial_marginCatalog polynomial_marginThreshold)
    GreedyFeasibleTable.polynomial_table

def initialViews (z : List ℕ×List ℕ) : List ℕ×List ℕ := originalViews (initialViewInput z)
def initialViewsRealizer : Realizer initialViews := composition initialViewInputRealizer originalViewsRealizer

theorem polynomial_initialViews : PolynomialTime initialViewsRealizer :=
  polynomial_composition polynomial_initialViewInput polynomial_originalViews

def initialCheck (z : List ℕ×List ℕ) : ProfileCheckData := prepareProfileInput (z,initialViews z)
def initialCheckRealizer : Realizer initialCheck :=
  composition (pair identity initialViewsRealizer) prepareProfileInputRealizer

theorem polynomial_initialCheck : PolynomialTime initialCheckRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_initialViews) polynomial_prepareProfileInput

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts SmallContextCoordinates FirstPaperPhysicalMarginal
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)

lemma originalViews_code (e : Fin q ≃ Cells (paperSmall r c)) (X : Table r c) :
    originalViews ((cellCatalog (paperSmall r c) e,d^20),matrixCode X.val)=
      stateCode r c e (tableState r c X) := by
  rw [tableState_code]
  have he : originalFirstView ((cellCatalog (paperSmall r c) e,d^20),matrixCode X.val)=
      List.ofFn (fun i => X.val (e i).val.1 (e i).val.2) := by
    simp only [originalFirstView,cellCatalog,List.map_ofFn]
    congr 1
    funext i
    exact matrixEntry_code X.val (e i).val.1 (e i).val.2
  unfold originalViews
  rw [he,complementValues_ofFn]

lemma initialViews_code (htotal : (∑ i,r i)=∑ j,c j) :
    initialViews (List.ofFn r,List.ofFn c)=stateCode r c (computedCellEquiv r c)
      (tableState r c (GreedyFeasibleTable.table r c htotal)) := by
  unfold initialViews initialViewInput
  rw [GreedyFeasibleTable.listMatrix_ofFn]
  have hc : marginCatalog (List.ofFn r,List.ofFn c)=cellCatalog (paperSmall r c) (computedCellEquiv r c) := by
    rw [computedCellEquiv_catalog]
    unfold marginCatalog
    rw [marginThreshold_ofFn]
    rfl
  rw [hc,marginThreshold_ofFn]
  exact originalViews_code r c (computedCellEquiv r c) (GreedyFeasibleTable.table r c htotal)

lemma initialCheck_code (htotal : (∑ i,r i)=∑ j,c j) :
    initialCheck (List.ofFn r,List.ofFn c)=stateCodeData r c (computedCellEquiv r c)
      (tableState r c (GreedyFeasibleTable.table r c htotal)) := by
  unfold initialCheck
  rw [initialViews_code r c htotal,prepareProfileInput_eq]

end
end ContingencyTables.SmallGraphProfiles

end OAI
