import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Tensors
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.StageCRegroup
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.Terminal
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStageCShapeProducts
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStageCProductRates
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.MatrixMapDecidable

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldStageCFinish

open MatrixMultiplication.Foundation AllFieldHistory AllFieldParameters AllFieldFiniteFamily
open CWStageCProducts
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

private def localMapWithFintypes {F : Type*} [Field F]
    {X Y Z X' Y' Z' : Type} [newX : Fintype X] [newY : Fintype Y] [newZ : Fintype Z]
    {oldX : Fintype X} {oldY : Fintype Y} {oldZ : Fintype Z}
    {T : Tensor F X Y Z} {Q : Tensor F X' Y' Z'}
    (M : @LocalMap F _ X Y Z X' Y' Z' oldX oldY oldZ T Q) :
    @LocalMap F _ X Y Z X' Y' Z' newX newY newZ T Q := by
  cases Subsingleton.elim oldX newX
  cases Subsingleton.elim oldY newY
  cases Subsingleton.elim oldZ newZ
  exact M

private def pairLocalMap {F : Type*} {H B W : Type} [Field F] [Fintype H]
    [Fintype B] [Fintype W] [DecidableEq H] [DecidableEq B] (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false)
    (T : H → B → Bool → Tensor F W W W) :
    LocalMap (AllFieldStageCRegroup.splitTensor count T)
      (AllFieldStageCRegroup.pairedTensor count T) where
  x := fun x s => if s = AllFieldStageCRegroup.unpair count hc x then 1 else 0
  y := fun y s => if s = AllFieldStageCRegroup.unpair count hc y then 1 else 0
  z := fun z s => if s = AllFieldStageCRegroup.unpair count hc z then 1 else 0
  coefficient := by
    have hp := Tensor.pullback_eq_restrict
      (AllFieldStageCRegroup.unpair (W := W) count hc)
      (AllFieldStageCRegroup.unpair (W := W) count hc)
      (AllFieldStageCRegroup.unpair (W := W) count hc)
      (AllFieldStageCRegroup.splitTensor count T)
    exact hp.symm.trans (AllFieldStageCRegroup.pullback_unpair count hc T)

private def shapeFactorMap (F : Type*) [Field F] (side : Fin 3)
    (placement : Equiv.Perm (Fin 3)) (count : Fin 4 → ℕ) :
    LocalMap (placedShapeChildProducts F side placement count)
      (Tensor.matrixCoefficients (RowWords (placement side) count)
        (MiddleWords (placement side) count) (ColumnWords (placement side) count)) :=
  LocalMap.ofExists (placedShapeChildProducts_restriction F side placement count)

private def shapeHistoryMap {F : Type*} {H : Type} [Field F] [Fintype H] [DecidableEq H]
    (side : H → Fin 3) (placement : H → Equiv.Perm (Fin 3))
    (count : H → Fin 4 → ℕ) :
    LocalMap (CommonDimensions.familyProduct (fun h =>
      placedShapeChildProducts F (side h) (placement h) (count h)))
      (Tensor.matrixCoefficients
        (HistoryRowWords (fun h => placement h (side h)) count)
        (HistoryMiddleWords (fun h => placement h (side h)) count)
        (HistoryColumnWords (fun h => placement h (side h)) count)) := by
  let M := AllFieldTerminal.terminalProductMap
    (F := F) (H := H)
    (X := fun h => Positions (count h) → ChildWords)
    (Y := fun h => Positions (count h) → ChildWords)
    (Z := fun h => Positions (count h) → ChildWords)
    (fun h => placedShapeChildProducts F (side h) (placement h) (count h))
    (fun h => RowWords (placement h (side h)) (count h))
    (fun h => MiddleWords (placement h (side h)) (count h))
    (fun h => ColumnWords (placement h (side h)) (count h))
    (fun h => LocalMap.redecideMatrix
      (shapeFactorMap F (side h) (placement h) (count h)) _ _ _)
  let N := localMapWithFintypes (F := F)
    (X := ∀ h, Positions (count h) → ChildWords)
    (Y := ∀ h, Positions (count h) → ChildWords)
    (Z := ∀ h, Positions (count h) → ChildWords)
    (newX := inferInstance) (newY := inferInstance) (newZ := inferInstance) M
  exact LocalMap.redecideMatrix N _ _ _

private theorem row_nonempty (s : Fin 3) (b : Fin 4) : Nonempty (Row s b) := by
  fin_cases s <;> fin_cases b <;>
    dsimp [Row, SmallRow, SmallInner] <;> infer_instance

private theorem middle_nonempty (s : Fin 3) (b : Fin 4) : Nonempty (Middle s b) := by
  fin_cases s <;> fin_cases b <;>
    dsimp [Middle, SmallRow, SmallInner] <;> infer_instance

private theorem column_nonempty (s : Fin 3) (b : Fin 4) : Nonempty (Column s b) := by
  fin_cases s <;> fin_cases b <;>
    dsimp [Column, SmallRow, SmallInner] <;> infer_instance

variable {K : ℕ} (allocation : Allocation) (dilation : ℕ)

abbrev Index (K : ℕ) := AfterC K × Placement

abbrev RawWords := ∀ h : Index K,
  HistoryWord allocation dilation (.afterC h.1, h.2)

def source (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (RawWords (K := K) allocation dilation)
      (RawWords (K := K) allocation dilation) (RawWords (K := K) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : Index K =>
    historyTensor F allocation dilation ε (.afterC h.1, h.2))

def counts (h : PopulationHistory K) (b : Fin 4) (right : Bool) : ℕ :=
  population allocation dilation (.afterC (h.1, b, right), h.2)

theorem counts_half (h : PopulationHistory K) (b : Fin 4) (right : Bool) :
    counts allocation dilation h b right = counts allocation dilation h b false :=
  branchPopulation_half allocation dilation (.stageC h.1, h.2) b right

@[simp] theorem counts_false (h : PopulationHistory K) (b : Fin 4) :
    counts allocation dilation h b false = populationAtomCounts allocation dilation h b := rfl

abbrev SingleWord := Fin 1 → Fin 7

def leaf (F : Type*) [Field F] (h : PopulationHistory K) (b : Fin 4) (right : Bool) :
    Tensor F SingleWord SingleWord SingleWord :=
  CWStrands.shapeTensor (Fin 1) (physicalShape h.2 (cShape (h.1, b, right)))

abbrev GroupedWords := AllFieldStageCRegroup.SplitWords
  (counts (K := K) allocation dilation) SingleWord

abbrev PairedWords := AllFieldStageCRegroup.PairedWords
  (counts (K := K) allocation dilation) SingleWord

def groupedSource (F : Type*) [Field F] :=
  AllFieldStageCRegroup.splitTensor (counts (K := K) allocation dilation) (leaf (K := K) F)

def pairedSource (F : Type*) [Field F] :
    Tensor F (PairedWords (K := K) allocation dilation)
      (PairedWords (K := K) allocation dilation) (PairedWords (K := K) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : PopulationHistory K =>
    placedShapeChildProducts F (stageCDistinguished (cShapeParent h.1)) h.2
      (populationAtomCounts allocation dilation h))

def indexEquiv : (PopulationHistory K × Fin 4 × Bool) ≃ Index K where
  toFun h := ((h.1.1, h.2.1, h.2.2), h.1.2)
  invFun h := ((h.1.1, h.2), h.1.2.1, h.1.2.2)
  left_inv h := by rcases h with ⟨⟨h, phi⟩, b, r⟩; rfl
  right_inv h := by rcases h with ⟨⟨h, b, r⟩, phi⟩; rfl

def toRaw (x : GroupedWords (K := K) allocation dilation) : RawWords (K := K) allocation dilation :=
  fun h => x (h.1.1, h.2) h.1.2.1 h.1.2.2

theorem regroup_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : GroupedWords (K := K) allocation dilation) :
    source allocation dilation F ε (toRaw allocation dilation x)
      (toRaw allocation dilation y) (toRaw allocation dilation z) =
      groupedSource allocation dilation F x y z := by
  change (∏ h : Index K, historyTensor F allocation dilation ε (.afterC h.1, h.2)
    (toRaw allocation dilation x h) (toRaw allocation dilation y h)
      (toRaw allocation dilation z h)) = _
  rw [← (indexEquiv (K := K)).prod_comp]
  simp only [Fintype.prod_prod_type]
  simp only [indexEquiv, Equiv.coe_fn_mk, toRaw, historyTensor_afterC,
    groupedSource, AllFieldStageCRegroup.splitTensor, CommonDimensions.familyProduct, leaf, counts,
    Fintype.prod_prod_type]

def regroupMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (source (K := K) allocation dilation F ε)
      (groupedSource (K := K) allocation dilation F) where
  x := fun x s => if s = toRaw allocation dilation x then 1 else 0
  y := fun y s => if s = toRaw allocation dilation y then 1 else 0
  z := fun z s => if s = toRaw allocation dilation z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    exact regroup_coefficient allocation dilation F ε x y z

theorem leaf_pair (F : Type*) [Field F] (h : PopulationHistory K) (b : Fin 4) :
    Tensor.product (leaf F h b false) (leaf F h b true) =
      placedShapeChildProduct F (stageCDistinguished (cShapeParent h.1)) h.2 b := by
  rw [placedShapeChildProduct_eq_stageC F (cShapeParent h.1)
    (bShape_size h.1.1.val) h.1.1.property]
  rfl

theorem pairedSource_eq (F : Type*) [Field F] :
    AllFieldStageCRegroup.pairedTensor (counts (K := K) allocation dilation) (leaf (K := K) F) =
      pairedSource (K := K) allocation dilation F := by
  funext x y z
  dsimp only [AllFieldStageCRegroup.pairedTensor, pairedSource, placedShapeChildProducts,
    CommonDimensions.familyProduct]
  apply Finset.prod_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro p _
  exact congrFun (congrFun (congrFun (leaf_pair F h p.1) (x h p)) (y h p)) (z h p)

attribute [local irreducible] AllFieldHistory.population

def pairMap (F : Type*) [Field F] :
    LocalMap (groupedSource (K := K) allocation dilation F)
      (pairedSource (K := K) allocation dilation F) := by
  let M := pairLocalMap (F := F) (H := PopulationHistory K) (B := Fin 4) (W := SingleWord)
    (counts (K := K) allocation dilation)
    (counts_half (K := K) allocation dilation) (leaf (K := K) F)
  let N : LocalMap (groupedSource (K := K) allocation dilation F)
      (AllFieldStageCRegroup.pairedTensor (counts (K := K) allocation dilation) (leaf (K := K) F)) :=
    localMapWithFintypes
      (X := GroupedWords (K := K) allocation dilation)
      (Y := GroupedWords (K := K) allocation dilation)
      (Z := GroupedWords (K := K) allocation dilation)
      (X' := PairedWords (K := K) allocation dilation)
      (Y' := PairedWords (K := K) allocation dilation)
      (Z' := PairedWords (K := K) allocation dilation) M
  exact ⟨N.x, N.y, N.z, N.coefficient.trans (pairedSource_eq (K := K) allocation dilation F)⟩

abbrev Rows := HistoryRowWords (populationSide (K := K)) (populationAtomCounts allocation dilation)
abbrev Middles := HistoryMiddleWords (populationSide (K := K)) (populationAtomCounts allocation dilation)
abbrev Columns := HistoryColumnWords (populationSide (K := K)) (populationAtomCounts allocation dilation)

def terminalMap (F : Type*) [Field F] :
    LocalMap (pairedSource (K := K) allocation dilation F)
      (Tensor.matrixCoefficients (Rows (K := K) allocation dilation)
        (Middles (K := K) allocation dilation) (Columns (K := K) allocation dilation)) := by
  let M := shapeHistoryMap (F := F) (H := PopulationHistory K)
    (fun h : PopulationHistory K => stageCDistinguished (cShapeParent h.1))
    (fun h => h.2) (populationAtomCounts allocation dilation)
  exact LocalMap.redecideMatrix (localMapWithFintypes M) _ _ _

def finishMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (source (K := K) allocation dilation F ε)
      (Tensor.matrixCoefficients (Rows (K := K) allocation dilation)
        (Middles (K := K) allocation dilation) (Columns (K := K) allocation dilation)) :=
  (regroupMap allocation dilation F ε).comp
    ((pairMap allocation dilation F).comp (terminalMap allocation dilation F))

theorem volume_eq_populationVolume :
    Fintype.card (Rows (K := K) allocation dilation) *
      Fintype.card (Middles (K := K) allocation dilation) *
        Fintype.card (Columns (K := K) allocation dilation) =
      populationVolume (K := K) allocation dilation := by
  simp only [Rows, Middles, Columns, populationVolume, historyVolume,
    HistoryRowWords, HistoryMiddleWords, HistoryColumnWords, Fintype.card_pi]

theorem rows_pos : 0 < Fintype.card (Rows (K := K) allocation dilation) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨fun h p => Classical.choice (row_nonempty (populationSide h) p.1)⟩

theorem middles_pos : 0 < Fintype.card (Middles (K := K) allocation dilation) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨fun h p => Classical.choice (middle_nonempty (populationSide h) p.1)⟩

theorem columns_pos : 0 < Fintype.card (Columns (K := K) allocation dilation) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨fun h p => Classical.choice (column_nonempty (populationSide h) p.1)⟩

end MatrixMultiplication.AllFieldStageCFinish

end

end OAI
