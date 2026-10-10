import Mathlib
import OAI.LinearAlgebra.MatrixFields.Arithmetic.MatrixMapDecidable
import OAI.LinearAlgebra.MatrixFields.Construction.FinalState
import OAI.LinearAlgebra.MatrixFields.Construction.ZeroFinish
import OAI.LinearAlgebra.MatrixFields.Entropy.ConstructionRates
import OAI.LinearAlgebra.MatrixFields.Entropy.RateLimit
import OAI.LinearAlgebra.MatrixFields.Histories.HistoryIteration

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialChoice

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily Filter
open scoped BigOperators Topology Classical

variable {K : ℕ}

structure Choice (allocation : Allocation) (m : ℕ) (δ : ℝ) where
  sample : AllFieldInitialFamily.Sample (K := K) allocation
    (δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ)) m
  selected : Finset (JointPopulation.Target (initialJointCounts (K := K) allocation m))
  card_selected : selected.card = AllFieldConstructionRates.initialCount (K := K) allocation δ m
  good : ∀ e ∈ selected, AllFieldInitialFamily.Good allocation
    (δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ)) m sample e

theorem initial_count_eq (allocation : Allocation) (m : ℕ) (δ : ℝ) :
    ⌊Real.exp ((populationLength (K := K) allocation m : ℝ) *
      ((K : ℝ) * AllFieldInitialEntropy.nativeH0 -
        δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ)))⌋₊ =
      AllFieldConstructionRates.initialCount (K := K) allocation δ m := by
  rw [AllFieldConstructionRates.initialCount_eq,
    AllFieldInitialFamily.populationLength_eq_mul_grid, Nat.cast_mul]
  congr 2
  change ((m : ℝ) * (AllFieldInitialFamily.grid (K := K) allocation : ℝ)) *
      ((K : ℝ) * AllFieldInitialEntropy.nativeH0 -
        δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ)) =
    (m : ℝ) * ((AllFieldInitialFamily.grid (K := K) allocation : ℝ) *
      ((K : ℝ) * AllFieldInitialEntropy.nativeH0) - δ)
  have hD : (AllFieldInitialFamily.grid (K := K) allocation : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (AllFieldInitialFamily.grid_pos allocation).ne'
  field_simp [hD]

theorem eventually_nonempty (allocation : Allocation) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, Nonempty (Choice (K := K) allocation m δ) := by
  have hs : 0 < δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ) :=
    div_pos hδ (Nat.cast_pos.mpr (AllFieldInitialFamily.grid_pos allocation))
  have h := AllFieldInitialFamily.eventually_exists_execution_with_width
    (K := K) allocation ℚ 0 hs
  filter_upwards [h] with m hm
  obtain ⟨sample, selected, hcard, hgood, _execution⟩ := hm
  exact ⟨{
    sample := sample
    selected := selected
    card_selected := hcard.trans (initial_count_eq allocation m δ)
    good := hgood }⟩

abbrev Tags (allocation : Allocation) (m : ℕ) (δ : ℝ)
    (choice : Choice (K := K) allocation m δ) :=
  AllFieldInitialHash.SelectedTargets (initialJointCounts (K := K) allocation m)
    choice.selected

@[simp] theorem card_tags (allocation : Allocation) (m : ℕ) (δ : ℝ)
    (choice : Choice (K := K) allocation m δ) :
    Fintype.card (Tags allocation m δ choice) =
      AllFieldConstructionRates.initialCount (K := K) allocation δ m := by
  rw [AllFieldInitialHash.selectedTargets_card]
  exact choice.card_selected

def execution (allocation : Allocation) (m : ℕ) (δ : ℝ)
    (choice : Choice (K := K) allocation m δ) (F : Type*) [Field F] (ε : ℝ) :
    Execution (cwSource F K (populationLength (K := K) allocation m))
      (Tensor.directSum (fun _ : Tags allocation m δ choice =>
        stateTensor F (K := K) allocation m ε 0)) :=
  AllFieldInitialFamily.executionWithWidth allocation F
    (δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ)) ε m
    choice.sample choice.selected choice.good

@[simp] theorem execution_copies (allocation : Allocation) (m : ℕ) (δ : ℝ)
    (choice : Choice (K := K) allocation m δ) (F : Type*) [Field F] (ε : ℝ) :
    Fintype.card (execution allocation m δ choice F ε).Copies = 1 := rfl

end MatrixMultiplication.AllFieldInitialChoice

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldTerminal

open MatrixMultiplication.Foundation AllFieldFiniteFamily CommonDimensions
open scoped BigOperators Classical

variable {F : Type*} {H : Type} [Field F] [Fintype H]
  {X Y Z : H → Type} [∀ h, Fintype (X h)] [∀ h, Fintype (Y h)] [∀ h, Fintype (Z h)]
  (T : ∀ h, Tensor F (X h) (Y h) (Z h)) (A B C : H → Type)
  [∀ h, Fintype (A h)] [∀ h, Fintype (B h)] [∀ h, Fintype (C h)]
  (maps : ∀ h, LocalMap (T h) (Tensor.matrixCoefficients (A h) (B h) (C h)))

def terminalProductMap :
    LocalMap (familyProduct T) (Tensor.matrixCoefficients (∀ h, A h) (∀ h, B h) (∀ h, C h)) :=
  LocalMap.ofExists (TerminalProducts.matrix_restriction_of_history_restrictions
    T A B C (fun h => (maps h).x) (fun h => (maps h).y) (fun h => (maps h).z)
    (fun h => (maps h).coefficient))

variable {I : Type} [Fintype I] {K N : ℕ}

def terminalExecution
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T))) :
    Execution (cwSource F K N)
      (AllFieldSource.matrixTarget F (Fintype.card (∀ h, A h))
        (Fintype.card (∀ h, B h)) (Fintype.card (∀ h, C h)) (Fintype.card I)) :=
  (E.restrict _ ((terminalProductMap T A B C maps).parallelCopies I)).restrict _
    (LocalMap.ofExists (TerminalRelabel.directSum_matrix_restrict_fin (K := F)
      I (∀ h, A h) (∀ h, B h) (∀ h, C h)))

@[simp] theorem terminalExecution_copies
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T))) :
    Fintype.card (terminalExecution T A B C maps E).Copies = Fintype.card E.Copies := rfl

def finish
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T)))
    (hA : 0 < Fintype.card (∀ h, A h)) (hB : 0 < Fintype.card (∀ h, B h))
    (hC : 0 < Fintype.card (∀ h, C h)) (hI : 0 < Fintype.card I) : AllFieldWitness F :=
  (terminalExecution T A B C maps E).toWitness hA hB hC hI

@[simp] theorem finish_multiplicity
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T)))
    (hA : 0 < Fintype.card (∀ h, A h)) (hB : 0 < Fintype.card (∀ h, B h))
    (hC : 0 < Fintype.card (∀ h, C h)) (hI : 0 < Fintype.card I) :
    (finish T A B C maps E hA hB hC hI).multiplicity = Fintype.card I := rfl

theorem finish_volume
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T)))
    (hA : 0 < Fintype.card (∀ h, A h)) (hB : 0 < Fintype.card (∀ h, B h))
    (hC : 0 < Fintype.card (∀ h, C h)) (hI : 0 < Fintype.card I) :
    (finish T A B C maps E hA hB hC hI).volume =
      ∏ h, Fintype.card (A h) * Fintype.card (B h) * Fintype.card (C h) := by
  change Fintype.card (∀ h, A h) * Fintype.card (∀ h, B h) *
    Fintype.card (∀ h, C h) = _
  simp only [Fintype.card_pi, Finset.prod_mul_distrib]

@[simp] theorem finish_rankBound
    (E : Execution (cwSource F K N) (Tensor.directSum (fun _ : I => familyProduct T)))
    (hA : 0 < Fintype.card (∀ h, A h)) (hB : 0 < Fintype.card (∀ h, B h))
    (hC : 0 < Fintype.card (∀ h, C h)) (hI : 0 < Fintype.card I) :
    (finish T A B C maps E hA hB hC hI).rankBound =
      AllFieldSource.rankBudget E.Copies K N := rfl

end MatrixMultiplication.AllFieldTerminal

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialZeroFinish

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldFiniteFamily
open AllFieldInitialLeafRates CWWindowedLeaves CWStrands CWZeroGeometry
open scoped BigOperators Classical

variable {K : ℕ}

abbrev Index (K : ℕ) := PopulationHistory K

local instance : DecidableEq (Index K) := Classical.decEq _

theorem shape_total (h : InitialZero K) : shapeTotal (initialShape h.val) = 16 :=
  (root_shape_spec _ (initialShape_mem h.val)).2

theorem has_zero (h : InitialZero K) : ∃ i, initialShape h.val i = 0 :=
  terminal_has_zero (.initial h.val) h.property

theorem canonical_axes_ne (h : InitialZero K) :
    zeroAxis (initialShape h.val) ≠ maxAxis (initialShape h.val) :=
  zero_ne_selected _ _ _ (by rw [shape_total]; norm_num)
    (zeroAxis_spec _ (has_zero h)) (maxAxis_spec _)

def zero (h : Index K) : Fin 3 := h.2 (zeroAxis (initialShape h.1.val))
def selected (h : Index K) : Fin 3 := h.2 (maxAxis (initialShape h.1.val))

theorem axes_ne (h : Index K) : zero h ≠ selected h :=
  fun he => canonical_axes_ne h.1 (h.2.injective he)

theorem weights_sum (h : InitialZero K) :
    shapeMax (initialShape h.val) + (16 - shapeMax (initialShape h.val)) = 2 * 8 := by
  simpa only [shape_total h] using max_add_complement (initialShape h.val)

theorem physical_shape_eq (h : Index K) :
    physicalShape h.2 (initialShape h.1.val) =
      CWOrientedZero.placedShape (zero h) (selected h)
        (shapeMax (initialShape h.1.val)) (16 - shapeMax (initialShape h.1.val)) := by
  simpa only [zero, selected, shape_total h.1] using
    physicalShape_eq_placedShape (initialShape h.1.val) h.2
      (zeroAxis (initialShape h.1.val)) (maxAxis (initialShape h.1.val))
      (zeroAxis_spec _ (has_zero h.1)) (maxAxis_spec _) (canonical_axes_ne h.1)

variable (allocation : Allocation) (dilation : ℕ)

def embed (h : Index K) (side : Fin 3) (w : Words allocation dilation h) :
    HistoryWord allocation dilation (.initial h.1.val, h.2) :=
  fun i => CWOrientedZero.sideWord (zero h) (selected h) side (w i)

theorem coefficient (F : Type*) [Field F] (ε : ℝ) (h : Index K)
    (x y z : Words allocation dilation h) :
    historyTensor F allocation dilation ε (.initial h.1.val, h.2)
      (embed allocation dilation h 0 x) (embed allocation dilation h 1 y)
      (embed allocation dilation h 2 z) =
      if CWOrientedZero.matched (zero h) x y z then 1 else 0 := by
  rw [historyTensor_initial, physical_shape_eq]
  exact CWOrientedZero.power_coefficient F 8 (shapeMax (initialShape h.1.val))
    (16 - shapeMax (initialShape h.1.val))
    (population allocation dilation (.initial h.1.val, h.2))
    (weights_sum h.1) (zero h) (selected h) (axes_ne h)
    (fun w : Words allocation dilation h => w) Function.injective_id x y z

abbrev RowIndex (h : Index K) := CWOrientedZero.Row (zero h) (Words allocation dilation h)
abbrev MiddleIndex (h : Index K) := CWOrientedZero.Middle (zero h) (Words allocation dilation h)
abbrev ColumnIndex (h : Index K) := CWOrientedZero.Column (zero h) (Words allocation dilation h)

def factorMap (F : Type*) [Field F] (ε : ℝ) (h : Index K) :
    LocalMap (historyTensor F allocation dilation ε (.initial h.1.val, h.2))
      (Tensor.matrixCoefficients (RowIndex allocation dilation h)
        (MiddleIndex allocation dilation h) (ColumnIndex allocation dilation h)) := by
  letI : Nonempty (Words allocation dilation h) :=
    Fintype.card_pos_iff.mp (card_words_pos allocation dilation h)
  exact CWOrientedZero.ofMatching F _ (zero h) (embed allocation dilation h)
    (coefficient allocation dilation F ε h)

theorem factor_volume (h : Index K) :
    Fintype.card (RowIndex allocation dilation h) *
      Fintype.card (MiddleIndex allocation dilation h) *
      Fintype.card (ColumnIndex allocation dilation h) =
      Fintype.card (Words allocation dilation h) :=
  CWOrientedZero.volume (zero h) (Words allocation dilation h)

abbrev RawWords := ∀ h : Index K,
  HistoryWord allocation dilation (.initial h.1.val, h.2)
abbrev Rows := ∀ h : Index K, RowIndex allocation dilation h
abbrev Middles := ∀ h : Index K, MiddleIndex allocation dilation h
abbrev Columns := ∀ h : Index K, ColumnIndex allocation dilation h

def source (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (RawWords (K := K) allocation dilation)
      (RawWords (K := K) allocation dilation) (RawWords (K := K) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : Index K =>
    historyTensor F allocation dilation ε (.initial h.1.val, h.2))

def finishMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (source (K := K) allocation dilation F ε)
      (Tensor.matrixCoefficients (Rows (K := K) allocation dilation)
        (Middles (K := K) allocation dilation) (Columns (K := K) allocation dilation)) :=
  AllFieldTerminal.terminalProductMap
    (H := Index K)
    (X := fun h => HistoryWord allocation dilation (.initial h.1.val, h.2))
    (Y := fun h => HistoryWord allocation dilation (.initial h.1.val, h.2))
    (Z := fun h => HistoryWord allocation dilation (.initial h.1.val, h.2))
    (fun h : Index K => historyTensor F allocation dilation ε (.initial h.1.val, h.2))
    (RowIndex allocation dilation) (MiddleIndex allocation dilation)
    (ColumnIndex allocation dilation) (factorMap allocation dilation F ε)

theorem volume_eq :
    Fintype.card (Rows (K := K) allocation dilation) *
      Fintype.card (Middles (K := K) allocation dilation) *
      Fintype.card (Columns (K := K) allocation dilation) =
      AllFieldInitialLeafRates.volume (K := K) allocation dilation := by
  rw [AllFieldInitialLeafRates.volume_eq_prod]
  simp only [Rows, Middles, Columns, Fintype.card_pi,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro h _
  simpa only [Words, Fintype.card_pi] using factor_volume allocation dilation h

theorem volume_pos :
    0 < Fintype.card (Rows (K := K) allocation dilation) *
      Fintype.card (Middles (K := K) allocation dilation) *
      Fintype.card (Columns (K := K) allocation dilation) := by
  rw [volume_eq]
  exact AllFieldInitialLeafRates.volume_pos allocation dilation

theorem rows_pos : 0 < Fintype.card (Rows (K := K) allocation dilation) :=
  Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right (volume_pos allocation dilation))

theorem middles_pos : 0 < Fintype.card (Middles (K := K) allocation dilation) :=
  Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right (volume_pos allocation dilation))

theorem columns_pos : 0 < Fintype.card (Columns (K := K) allocation dilation) :=
  Nat.pos_of_mul_pos_left (volume_pos allocation dilation)

end MatrixMultiplication.AllFieldInitialZeroFinish

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.CommonDimensions

namespace MatrixMultiplication.AllFieldStageCRegroup

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H B W F : Type*}

abbrev Positions (count : H → B → Bool → ℕ) (h : H) :=
  Σ b : B, Fin (count h b false)

abbrev PairedWords (count : H → B → Bool → ℕ) (W : Type*) :=
  ∀ h, Positions count h → W × W

abbrev SplitWords (count : H → B → Bool → ℕ) (W : Type*) :=
  ∀ h b r, Fin (count h b r) → W

def unpair (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false)
    (x : PairedWords count W) : SplitWords count W :=
  fun h b r i =>
    if r then (x h ⟨b, Fin.cast (hc h b r) i⟩).2
    else (x h ⟨b, Fin.cast (hc h b r) i⟩).1

def pair (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false)
    (x : SplitWords count W) : PairedWords count W :=
  fun h p => (x h p.1 false p.2, x h p.1 true (Fin.cast (hc h p.1 true).symm p.2))

theorem pair_unpair (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false)
    (x : PairedWords count W) : pair count hc (unpair count hc x) = x := by
  funext h p
  rfl

theorem unpair_pair (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false)
    (x : SplitWords count W) : unpair count hc (pair count hc x) = x := by
  funext h b r i
  cases r <;> rfl

def unpairEquiv (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false) :
    PairedWords count W ≃ SplitWords count W where
  toFun := unpair count hc
  invFun := pair count hc
  left_inv := pair_unpair count hc
  right_inv := unpair_pair count hc

variable [Fintype H] [Fintype B] [CommSemiring F]

def splitTensor (count : H → B → Bool → ℕ) (T : H → B → Bool → Tensor F W W W) :
    Tensor F (SplitWords count W) (SplitWords count W) (SplitWords count W) :=
  familyProduct fun h => familyProduct fun b => familyProduct fun r =>
    Tensor.power (T h b r) (count h b r)

def pairedTensor (count : H → B → Bool → ℕ) (T : H → B → Bool → Tensor F W W W) :
    Tensor F (PairedWords count W) (PairedWords count W) (PairedWords count W) :=
  familyProduct fun h => familyProduct fun p : Positions count h =>
    Tensor.product (T h p.1 false) (T h p.1 true)

private theorem prod_fin_cast {m n : ℕ} (e : m = n) (f : Fin n → F) :
    (∏ i : Fin m, f (Fin.cast e i)) = ∏ i : Fin n, f i := by
  subst n
  rfl

theorem pullback_unpair (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false)
    (T : H → B → Bool → Tensor F W W W) :
    Tensor.pullback (unpair count hc) (unpair count hc) (unpair count hc)
      (splitTensor count T) = pairedTensor count T := by
  funext x y z
  simp only [Tensor.pullback, splitTensor, pairedTensor, familyProduct]
  apply Finset.prod_congr rfl
  intro h _
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro b _
  rw [Fintype.prod_bool]
  change
    (∏ j : Fin (count h b true), T h b true
      (x h ⟨b, Fin.cast (hc h b true) j⟩).2
      (y h ⟨b, Fin.cast (hc h b true) j⟩).2
      (z h ⟨b, Fin.cast (hc h b true) j⟩).2) *
    (∏ j : Fin (count h b false), T h b false
      (x h ⟨b, j⟩).1 (y h ⟨b, j⟩).1 (z h ⟨b, j⟩).1) =
    ∏ j : Fin (count h b false),
      T h b false (x h ⟨b, j⟩).1 (y h ⟨b, j⟩).1 (z h ⟨b, j⟩).1 *
      T h b true (x h ⟨b, j⟩).2 (y h ⟨b, j⟩).2 (z h ⟨b, j⟩).2
  rw [prod_fin_cast (hc h b true) (fun j =>
    T h b true (x h ⟨b, j⟩).2 (y h ⟨b, j⟩).2 (z h ⟨b, j⟩).2),
    Finset.prod_mul_distrib]
  exact mul_comm _ _

end MatrixMultiplication.AllFieldStageCRegroup

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldStageCFinish

open MatrixMultiplication.Foundation AllFieldHistory AllFieldParameters AllFieldFiniteFamily
open CWStageCProducts
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

private def localMapWithFintypes_inline_MatrixMultiplication_AllFieldStageCFinish {F : Type*} [Field F]
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
  let N := localMapWithFintypes_inline_MatrixMultiplication_AllFieldStageCFinish (F := F)
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
    localMapWithFintypes_inline_MatrixMultiplication_AllFieldStageCFinish
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
  exact LocalMap.redecideMatrix (localMapWithFintypes_inline_MatrixMultiplication_AllFieldStageCFinish M) _ _ _

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
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldFinishedWitness

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldTerminalStatisticLaws AllFieldTerminalRates
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

private def localMapWithFintypes_inline_MatrixMultiplication_AllFieldFinishedWitness {F : Type*} [Field F]
    {X Y Z X' Y' Z' : Type} [newX : Fintype X] [newY : Fintype Y] [newZ : Fintype Z]
    {oldX : Fintype X} {oldY : Fintype Y} {oldZ : Fintype Z}
    {T : Tensor F X Y Z} {Q : Tensor F X' Y' Z'}
    (M : @LocalMap F _ X Y Z X' Y' Z' oldX oldY oldZ T Q) :
    @LocalMap F _ X Y Z X' Y' Z' newX newY newZ T Q := by
  cases Subsingleton.elim oldX newX
  cases Subsingleton.elim oldY newY
  cases Subsingleton.elim oldZ newZ
  exact M

private def matrixProductMap (F : Type*) [Field F]
    (A B C D E G : Type) [Fintype A] [Fintype B] [Fintype C]
    [Fintype D] [Fintype E] [Fintype G] :
    LocalMap (Tensor.product (Tensor.matrixCoefficients (K := F) A B C)
      (Tensor.matrixCoefficients D E G))
      (Tensor.matrixCoefficients (A × D) (B × E) (C × G)) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
    (fun y : (B × E) × (C × G) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
    (fun z : (C × G) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2))) _).symm.trans ?_⟩
  funext x y z
  exact Tensor.matrixCoefficients_product x y z

private def combineMatrixMaps {F : Type*} [Field F]
    {X Y Z U V W A B C D E G : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype G]
    {T : Tensor F X Y Z} {Q : Tensor F U V W}
    (first : LocalMap T (Tensor.matrixCoefficients A B C))
    (second : LocalMap Q (Tensor.matrixCoefficients D E G)) :
    LocalMap (Tensor.product T Q)
      (Tensor.matrixCoefficients (A × D) (B × E) (C × G)) :=
  (first.product second).comp (matrixProductMap F A B C D E G)

variable {K : ℕ} (allocation : Allocation) (m : ℕ)

abbrev ZeroRows := ∀ h : TerminalZero K, AllFieldZeroFinish.Row allocation m h
abbrev ZeroMiddles := ∀ h : TerminalZero K, AllFieldZeroFinish.Middle allocation m h
abbrev ZeroColumns := ∀ h : TerminalZero K, AllFieldZeroFinish.Column allocation m h

abbrev Rows := AllFieldInitialZeroFinish.Rows (K := K) allocation (terminalDilation K m) ×
  (ZeroRows (K := K) allocation m ×
    AllFieldStageCFinish.Rows (K := K) allocation (terminalDilation K m))
abbrev Middles := AllFieldInitialZeroFinish.Middles (K := K) allocation (terminalDilation K m) ×
  (ZeroMiddles (K := K) allocation m ×
    AllFieldStageCFinish.Middles (K := K) allocation (terminalDilation K m))
abbrev Columns := AllFieldInitialZeroFinish.Columns (K := K) allocation (terminalDilation K m) ×
  (ZeroColumns (K := K) allocation m ×
    AllFieldStageCFinish.Columns (K := K) allocation (terminalDilation K m))

local instance initialRowsFintype :
    Fintype (AllFieldInitialZeroFinish.Rows (K := K) allocation (terminalDilation K m)) := by
  letI : DecidableEq (AllFieldInitialZeroFinish.Index K) := Classical.decEq _
  exact inferInstanceAs (Fintype (∀ h : AllFieldInitialZeroFinish.Index K,
    AllFieldInitialZeroFinish.RowIndex allocation (terminalDilation K m) h))

local instance initialMiddlesFintype :
    Fintype (AllFieldInitialZeroFinish.Middles (K := K) allocation (terminalDilation K m)) := by
  letI : DecidableEq (AllFieldInitialZeroFinish.Index K) := Classical.decEq _
  exact inferInstanceAs (Fintype (∀ h : AllFieldInitialZeroFinish.Index K,
    AllFieldInitialZeroFinish.MiddleIndex allocation (terminalDilation K m) h))

local instance initialColumnsFintype :
    Fintype (AllFieldInitialZeroFinish.Columns (K := K) allocation (terminalDilation K m)) := by
  letI : DecidableEq (AllFieldInitialZeroFinish.Index K) := Classical.decEq _
  exact inferInstanceAs (Fintype (∀ h : AllFieldInitialZeroFinish.Index K,
    AllFieldInitialZeroFinish.ColumnIndex allocation (terminalDilation K m) h))

local instance stageCRowsFintype :
    Fintype (AllFieldStageCFinish.Rows (K := K) allocation (terminalDilation K m)) := by
  exact inferInstanceAs (Fintype (∀ h : CWStageCProducts.PopulationHistory K,
    CWStageCProducts.RowWords (CWStageCProducts.populationSide h)
      (CWStageCProducts.populationAtomCounts allocation (terminalDilation K m) h)))

local instance stageCMiddlesFintype :
    Fintype (AllFieldStageCFinish.Middles (K := K) allocation (terminalDilation K m)) := by
  exact inferInstanceAs (Fintype (∀ h : CWStageCProducts.PopulationHistory K,
    CWStageCProducts.MiddleWords (CWStageCProducts.populationSide h)
      (CWStageCProducts.populationAtomCounts allocation (terminalDilation K m) h)))

local instance stageCColumnsFintype :
    Fintype (AllFieldStageCFinish.Columns (K := K) allocation (terminalDilation K m)) := by
  exact inferInstanceAs (Fintype (∀ h : CWStageCProducts.PopulationHistory K,
    CWStageCProducts.ColumnWords (CWStageCProducts.populationSide h)
      (CWStageCProducts.populationAtomCounts allocation (terminalDilation K m) h)))

local instance rowsFintype : Fintype (Rows (K := K) allocation m) :=
  inferInstanceAs (Fintype
    (AllFieldInitialZeroFinish.Rows (K := K) allocation (terminalDilation K m) ×
      (ZeroRows (K := K) allocation m ×
        AllFieldStageCFinish.Rows (K := K) allocation (terminalDilation K m))))

local instance middlesFintype : Fintype (Middles (K := K) allocation m) :=
  inferInstanceAs (Fintype
    (AllFieldInitialZeroFinish.Middles (K := K) allocation (terminalDilation K m) ×
      (ZeroMiddles (K := K) allocation m ×
        AllFieldStageCFinish.Middles (K := K) allocation (terminalDilation K m))))

local instance columnsFintype : Fintype (Columns (K := K) allocation m) :=
  inferInstanceAs (Fintype
    (AllFieldInitialZeroFinish.Columns (K := K) allocation (terminalDilation K m) ×
      (ZeroColumns (K := K) allocation m ×
        AllFieldStageCFinish.Columns (K := K) allocation (terminalDilation K m))))

local instance initialRawFintype :
    Fintype (AllFieldFinalState.InitialWords (K := K) allocation (terminalDilation K m)) :=
  inferInstanceAs (Fintype (∀ h : AllFieldFinalState.InitialIndex K,
    HistoryWord allocation (terminalDilation K m) (.initial h.1.val, h.2)))

local instance zeroRawFintype :
    Fintype (AllFieldFinalState.ZeroWords (K := K) allocation (terminalDilation K m)) :=
  inferInstanceAs (Fintype (∀ h : TerminalZero K,
    HistoryWord allocation (terminalDilation K m) (AllFieldTerminalStatisticLaws.history h)))

local instance stageCRawFintype :
    Fintype (AllFieldFinalState.CWords (K := K) allocation (terminalDilation K m)) :=
  inferInstanceAs (Fintype (∀ h : AllFieldFinalState.CIndex K,
    HistoryWord allocation (terminalDilation K m) (.afterC h.1, h.2)))

theorem zero_volume :
    Fintype.card (ZeroRows (K := K) allocation m) *
      Fintype.card (ZeroMiddles (K := K) allocation m) *
        Fintype.card (ZeroColumns (K := K) allocation m) = zeroVolume (K := K) allocation m := by
  simp only [ZeroRows, ZeroMiddles, ZeroColumns, Fintype.card_pi, zeroVolume]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun h _ => AllFieldZeroFinish.volume allocation m h

theorem volume_eq :
    Fintype.card (Rows (K := K) allocation m) *
      Fintype.card (Middles (K := K) allocation m) *
        Fintype.card (Columns (K := K) allocation m) = terminalVolume (K := K) allocation m := by
  simp only [Rows, Middles, Columns, Fintype.card_prod]
  calc
    _ = (Fintype.card (AllFieldInitialZeroFinish.Rows (K := K) allocation (terminalDilation K m)) *
          Fintype.card (AllFieldInitialZeroFinish.Middles (K := K) allocation (terminalDilation K m)) *
          Fintype.card (AllFieldInitialZeroFinish.Columns (K := K) allocation (terminalDilation K m))) *
        (Fintype.card (ZeroRows (K := K) allocation m) *
          Fintype.card (ZeroMiddles (K := K) allocation m) *
          Fintype.card (ZeroColumns (K := K) allocation m)) *
        (Fintype.card (AllFieldStageCFinish.Rows (K := K) allocation (terminalDilation K m)) *
          Fintype.card (AllFieldStageCFinish.Middles (K := K) allocation (terminalDilation K m)) *
          Fintype.card (AllFieldStageCFinish.Columns (K := K) allocation (terminalDilation K m))) := by ring
    _ = _ := by rw [AllFieldInitialZeroFinish.volume_eq, zero_volume,
      AllFieldStageCFinish.volume_eq_populationVolume]; rfl

theorem dimensions_pos :
    0 < Fintype.card (Rows (K := K) allocation m) ∧
      0 < Fintype.card (Middles (K := K) allocation m) ∧
        0 < Fintype.card (Columns (K := K) allocation m) := by
  have hp := terminalVolume_pos (K := K) allocation m
  rw [← volume_eq allocation m] at hp
  have hab := Nat.pos_of_mul_pos_right hp
  exact ⟨Nat.pos_of_mul_pos_right hab, Nat.pos_of_mul_pos_left hab,
    Nat.pos_of_mul_pos_left hp⟩

def zeroMap (F : Type*) [Field F] {ε : ℝ} (hm : 0 < m) (hε : 0 ≤ ε) :
    LocalMap (AllFieldFinalState.zeroTensor (K := K) allocation (terminalDilation K m) F ε)
      (Tensor.matrixCoefficients (ZeroRows (K := K) allocation m)
        (ZeroMiddles (K := K) allocation m) (ZeroColumns (K := K) allocation m)) := by
  let result := AllFieldTerminal.terminalProductMap
    (fun h : TerminalZero K => historyTensor F allocation (terminalDilation K m) ε
      (AllFieldTerminalStatisticLaws.history h))
    (fun h => AllFieldZeroFinish.Row allocation m h)
    (fun h => AllFieldZeroFinish.Middle allocation m h)
    (fun h => AllFieldZeroFinish.Column allocation m h)
    (fun h => LocalMap.redecideMatrix
      (AllFieldZeroFinish.localMap F allocation hm hε h) _ _ _)
  let aligned := localMapWithFintypes_inline_MatrixMultiplication_AllFieldFinishedWitness (F := F)
    (X := AllFieldFinalState.ZeroWords (K := K) allocation (terminalDilation K m))
    (Y := AllFieldFinalState.ZeroWords (K := K) allocation (terminalDilation K m))
    (Z := AllFieldFinalState.ZeroWords (K := K) allocation (terminalDilation K m))
    (newX := inferInstance) (newY := inferInstance) (newZ := inferInstance) result
  exact LocalMap.redecideMatrix aligned _ _ _

def terminalMap (F : Type*) [Field F] {ε : ℝ} (hm : 0 < m) (hε : 0 ≤ ε) :
    LocalMap (stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2))
      (Tensor.matrixCoefficients (Rows (K := K) allocation m)
        (Middles (K := K) allocation m) (Columns (K := K) allocation m)) := by
  let initialAligned := localMapWithFintypes_inline_MatrixMultiplication_AllFieldFinishedWitness (F := F)
    (X := AllFieldInitialZeroFinish.RawWords (K := K) allocation (terminalDilation K m))
    (Y := AllFieldInitialZeroFinish.RawWords (K := K) allocation (terminalDilation K m))
    (Z := AllFieldInitialZeroFinish.RawWords (K := K) allocation (terminalDilation K m))
    (newX := inferInstance) (newY := inferInstance) (newZ := inferInstance)
    (AllFieldInitialZeroFinish.finishMap (K := K) allocation (terminalDilation K m) F ε)
  let initial := LocalMap.redecideMatrix initialAligned
    (Classical.decEq _) (Classical.decEq _) (Classical.decEq _)
  let zeros := LocalMap.redecideMatrix (zeroMap (K := K) allocation m F hm hε)
    (Classical.decEq _) (Classical.decEq _) (Classical.decEq _)
  let interior := LocalMap.redecideMatrix
    (AllFieldStageCFinish.finishMap (K := K) allocation (terminalDilation K m) F ε)
    (Classical.decEq _) (Classical.decEq _) (Classical.decEq _)
  let second := LocalMap.redecideMatrix
    (combineMatrixMaps zeros interior)
    (Classical.decEq _) (Classical.decEq _) (Classical.decEq _)
  let third := combineMatrixMaps initial second
  exact LocalMap.redecideMatrix
    ((AllFieldFinalState.map (K := K) allocation (terminalDilation K m) F ε).comp third) _ _ _

variable {F : Type*} [Field F] {ε : ℝ} {I : Type} [Fintype I]

def execution (hm : 0 < m) (hε : 0 ≤ ε)
    (E : Execution (cwSource F K (terminalLength allocation K m))
      (Tensor.directSum (fun _ : I =>
        stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2)))) :
    Execution (cwSource F K (terminalLength allocation K m))
      (AllFieldSource.matrixTarget F (Fintype.card (Rows (K := K) allocation m))
        (Fintype.card (Middles (K := K) allocation m))
        (Fintype.card (Columns (K := K) allocation m)) (Fintype.card I)) :=
  (E.restrict _ ((terminalMap allocation m F hm hε).parallelCopies I)).restrict _
    (LocalMap.ofExists (TerminalRelabel.directSum_matrix_restrict_fin (K := F)
      I (Rows (K := K) allocation m) (Middles (K := K) allocation m)
        (Columns (K := K) allocation m)))

def witness (hm : 0 < m) (hε : 0 ≤ ε)
    (E : Execution (cwSource F K (terminalLength allocation K m))
      (Tensor.directSum (fun _ : I =>
        stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2))))
    (hI : 0 < Fintype.card I) : AllFieldWitness F :=
  (execution allocation m hm hε E).toWitness
    (dimensions_pos allocation m).1 (dimensions_pos allocation m).2.1
    (dimensions_pos allocation m).2.2 hI

@[simp] theorem witness_volume (hm : 0 < m) (hε : 0 ≤ ε)
    (E : Execution (cwSource F K (terminalLength allocation K m))
      (Tensor.directSum (fun _ : I =>
        stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2))))
    (hI : 0 < Fintype.card I) :
    (witness allocation m hm hε E hI).volume = terminalVolume (K := K) allocation m :=
  volume_eq allocation m

@[simp] theorem witness_multiplicity (hm : 0 < m) (hε : 0 ≤ ε)
    (E : Execution (cwSource F K (terminalLength allocation K m))
      (Tensor.directSum (fun _ : I =>
        stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2))))
    (hI : 0 < Fintype.card I) :
    (witness allocation m hm hε E hI).multiplicity = Fintype.card I := rfl

@[simp] theorem witness_rankBound (hm : 0 < m) (hε : 0 ≤ ε)
    (E : Execution (cwSource F K (terminalLength allocation K m))
      (Tensor.directSum (fun _ : I =>
        stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2))))
    (hI : 0 < Fintype.card I) :
    (witness allocation m hm hε E hI).rankBound =
      AllFieldSource.rankBudget E.Copies K (terminalLength allocation K m) := rfl

end MatrixMultiplication.AllFieldFinishedWitness

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldConstructionData

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : ℕ}

structure Data (allocation : Allocation) (dilation : ℕ) (width slack : ℝ) where
  initial : AllFieldInitialChoice.Choice (K := K) allocation dilation slack
  groups : AllFieldHistoryIteration.ScheduleChoices
    (K := K) allocation dilation width slack
  threshold : ∀ t : Fin (K + 2),
    AllFieldHistoryRecovery.minimumDilation (K := K) (tick := t.val) allocation width ≤ dilation

variable (allocation : Allocation) (dilation : ℕ) (width slack : ℝ)

abbrev Tags (data : Data (K := K) allocation dilation width slack) :=
  AllFieldHistoryIteration.Tags allocation dilation width slack
    (AllFieldInitialChoice.Tags allocation dilation slack data.initial) data.groups

instance tagsFintype (data : Data (K := K) allocation dilation width slack) :
    Fintype (Tags allocation dilation width slack data) := inferInstance

def execution (F : Type*) [Field F] (hwidth : 0 < width)
    (data : Data (K := K) allocation dilation width slack) :
    Execution (cwSource F K (populationLength (K := K) allocation dilation))
      (Tensor.directSum (fun _ : Tags allocation dilation width slack data =>
        stateTensor F (K := K) allocation dilation width (K + 2))) :=
  AllFieldHistoryIteration.execution allocation dilation width slack F hwidth
    data.threshold data.groups
    (AllFieldInitialChoice.execution allocation dilation slack data.initial F width)

theorem card_tags (data : Data (K := K) allocation dilation width slack) :
    Fintype.card (Tags allocation dilation width slack data) =
      Fintype.card (AllFieldConstructionRates.SelectedLabels
        (K := K) allocation slack dilation) := by
  rw [AllFieldHistoryIteration.card_tags, AllFieldInitialChoice.card_tags,
    AllFieldConstructionRates.card_selected]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  apply Finset.prod_congr rfl
  intro sigma _
  exact (AllFieldConstructionRates.groupCount_eq_native allocation slack dilation t sigma).symm

theorem execution_copies (F : Type*) [Field F] (hwidth : 0 < width)
    (data : Data (K := K) allocation dilation width slack) :
    Fintype.card (execution allocation dilation width slack F hwidth data).Copies =
      Fintype.card (AllFieldConstructionRates.Copies
        (K := K) allocation width dilation) := by
  rw [execution, AllFieldHistoryIteration.execution_copies,
    AllFieldInitialChoice.execution_copies, one_mul]
  simp only [AllFieldConstructionRates.Copies, Fintype.card_pi,
    InverseLinearRecovery.MaskRectangles, ExactRecovery.card_mask_rectangles, Fintype.card_fin]

theorem tags_pos
    (hslack : ∀ slot : AllFieldConstructionRates.Slot K,
      slack ≤ (AllFieldConstructionRates.denominator (K := K) allocation : ℝ) *
        AllFieldConstructionRates.capacity allocation slot)
    (data : Data (K := K) allocation dilation width slack) :
    0 < Fintype.card (Tags allocation dilation width slack data) := by
  rw [card_tags]
  exact AllFieldConstructionRates.selected_pos allocation slack hslack dilation

variable {F : Type*} [Field F] (m : ℕ)

def witness (hm : 0 < m) (hwidth : 0 < width)
    (hslack : ∀ slot : AllFieldConstructionRates.Slot K,
      slack ≤ (AllFieldConstructionRates.denominator (K := K) allocation : ℝ) *
        AllFieldConstructionRates.capacity allocation slot)
    (data : Data (K := K) allocation
      (AllFieldTerminalRates.terminalDilation K m) width slack) : AllFieldWitness F :=
  AllFieldFinishedWitness.witness allocation m hm hwidth.le
    (execution allocation (AllFieldTerminalRates.terminalDilation K m) width slack F hwidth data)
    (tags_pos allocation (AllFieldTerminalRates.terminalDilation K m) width slack hslack data)

@[simp] theorem witness_volume (hm : 0 < m) (hwidth : 0 < width)
    (hslack : ∀ slot : AllFieldConstructionRates.Slot K,
      slack ≤ (AllFieldConstructionRates.denominator (K := K) allocation : ℝ) *
        AllFieldConstructionRates.capacity allocation slot)
    (data : Data (K := K) allocation
      (AllFieldTerminalRates.terminalDilation K m) width slack) :
    (witness (F := F) allocation width slack m hm hwidth hslack data).volume =
      AllFieldTerminalRates.terminalVolume (K := K) allocation m :=
  AllFieldFinishedWitness.witness_volume _ _ _ _ _ _

@[simp] theorem witness_multiplicity (hm : 0 < m) (hwidth : 0 < width)
    (hslack : ∀ slot : AllFieldConstructionRates.Slot K,
      slack ≤ (AllFieldConstructionRates.denominator (K := K) allocation : ℝ) *
        AllFieldConstructionRates.capacity allocation slot)
    (data : Data (K := K) allocation
      (AllFieldTerminalRates.terminalDilation K m) width slack) :
    (witness (F := F) allocation width slack m hm hwidth hslack data).multiplicity =
      Fintype.card (AllFieldConstructionRates.SelectedLabels
        (K := K) allocation slack (AllFieldTerminalRates.terminalDilation K m)) := by
  change Fintype.card (Tags _ _ _ _ data) = _
  exact card_tags _ _ _ _ data

@[simp] theorem witness_rankBound (hm : 0 < m) (hwidth : 0 < width)
    (hslack : ∀ slot : AllFieldConstructionRates.Slot K,
      slack ≤ (AllFieldConstructionRates.denominator (K := K) allocation : ℝ) *
        AllFieldConstructionRates.capacity allocation slot)
    (data : Data (K := K) allocation
      (AllFieldTerminalRates.terminalDilation K m) width slack) :
    (witness (F := F) allocation width slack m hm hwidth hslack data).rankBound =
      AllFieldSource.rankBudget
        (AllFieldConstructionRates.Copies (K := K) allocation width
          (AllFieldTerminalRates.terminalDilation K m)) K
        (AllFieldTerminalRates.terminalLength allocation K m) := by
  change AllFieldSource.rankBudget
    (execution allocation (AllFieldTerminalRates.terminalDilation K m) width slack F hwidth data).Copies
    K (AllFieldTerminalRates.terminalLength allocation K m) = _
  unfold AllFieldSource.rankBudget
  rw [execution_copies]

end MatrixMultiplication.AllFieldConstructionData

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldConstructionFamily

open MatrixMultiplication.Foundation AllFieldHistory AllFieldConstructionData
open AllFieldConstructionRates Filter
open scoped BigOperators Topology Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : ℕ}

theorem exists_width_eventually_data (allocation : Allocation)
    {slack widthMax : ℝ} (hslack : 0 < slack) (hmax : 0 < widthMax) :
    ∃ width : ℝ, 0 < width ∧ width ≤ widthMax ∧
      ∀ᶠ m : ℕ in atTop, Nonempty (Data (K := K) allocation m width slack) := by
  let Index := Fin (K + 2) × Placement
  have hindex : (Finset.univ : Finset Index).Nonempty :=
    ⟨(⟨0, by omega⟩, Equiv.refl _), Finset.mem_univ _⟩
  have hb (i : Index) :=
    AllFieldGroupSelection.exists_threshold_eventually_selected
      (K := K) (tick := i.1.val) allocation i.2 hslack hmax
  choose threshold hpositive hmaximum hselected using hb
  let width := Finset.univ.inf' hindex threshold
  have hwidth : 0 < width := by
    apply (Finset.lt_inf'_iff hindex).mpr
    intro i _
    exact hpositive i
  have hbound (i : Index) : width ≤ threshold i :=
    Finset.inf'_le _ (Finset.mem_univ i)
  have hwidthMax : width ≤ widthMax :=
    (hbound hindex.choose).trans (hmaximum hindex.choose)
  have hgroups : ∀ᶠ m : ℕ in atTop, ∀ i : Index,
      Nonempty (AllFieldGroupSelection.Selected (K := K) (tick := i.1.val)
        allocation m width i.2 slack) :=
    Filter.eventually_all.mpr (fun i => hselected i width hwidth (hbound i))
  have hthresholds : ∀ᶠ m : ℕ in atTop, ∀ t : Fin (K + 2),
      AllFieldHistoryRecovery.minimumDilation (K := K) (tick := t.val) allocation width ≤ m :=
    Filter.eventually_all.mpr (fun _ => eventually_ge_atTop _)
  refine ⟨width, hwidth, hwidthMax, ?_⟩
  filter_upwards [AllFieldInitialChoice.eventually_nonempty (K := K) allocation hslack,
    hgroups, hthresholds] with m hinitial hgroup hthreshold
  exact ⟨{ initial := Classical.choice hinitial
           groups := fun t sigma => Classical.choice (hgroup (t, sigma))
           threshold := hthreshold }⟩

def yieldRate (allocation : Allocation) (slack : ℝ) : ℝ :=
  AllFieldInitialEntropy.nativeH0 + AllFieldScheduledYield.physicalYield K allocation / K -
    (1 + 6 * (K + 2) : ℕ) * slack /
      ((K : ℝ) * denominator (K := K) allocation)

theorem exists_family (F : Type*) [Field F] (hK : 0 < K)
    (allocation : Allocation) {slack : ℝ} (hslack : 0 < slack)
    (hslots : ∀ slot : Slot K, slack ≤ (denominator (K := K) allocation : ℝ) *
      capacity allocation slot) :
    ∃ (W : ℕ → AllFieldWitness F) (scale : ℕ → ℝ),
      AllFieldRateLimit.HasRates W scale (yieldRate (K := K) allocation slack)
        AllFieldTerminalRates.S (8 * Real.log 7) := by
  obtain ⟨width, hwidth, _hmax, hd⟩ := exists_width_eventually_data
    (K := K) allocation hslack (show (0 : ℝ) < 1 by norm_num)
  have hterminal := (terminalDilation_tendsto K).eventually hd
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (hterminal.and (eventually_gt_atTop (0 : ℕ)))
  let data (n : ℕ) : Data (K := K) allocation
      (AllFieldTerminalRates.terminalDilation K (n + M)) width slack :=
    Classical.choice (hM (n + M) (by omega)).1
  have hn (n : ℕ) : 0 < n + M := (hM (n + M) (by omega)).2
  let W (n : ℕ) := witness (F := F) allocation width slack (n + M)
    (hn n) hwidth hslots (data n)
  let scale (n : ℕ) : ℝ := (K : ℝ) *
    AllFieldTerminalRates.terminalLength allocation K (n + M)
  refine ⟨W, scale, ?_⟩
  refine { scale_positive := ?_, yield_limit := ?_, volume_limit := ?_, rank_limit := ?_ }
  · apply Eventually.of_forall
    intro n
    exact mul_pos (Nat.cast_pos.mpr hK)
      (Nat.cast_pos.mpr (AllFieldTerminalRates.terminalLength_pos allocation (hn n)))
  · have h := (selected_terminal_rate hK allocation slack hslots).comp
      (tendsto_add_atTop_nat M)
    apply h.congr
    intro n
    simp only [Function.comp_def, W, scale, witness_multiplicity]
  · have h := (AllFieldTerminalRates.tendsto_terminalVolume hK allocation).comp
      (tendsto_add_atTop_nat M)
    apply h.congr
    intro n
    simp only [Function.comp_def, W, scale, witness_volume]
  · have h := (source_rank_terminal_rate hK allocation width).comp
      (tendsto_add_atTop_nat M)
    apply h.congr
    intro n
    simp only [Function.comp_def, W, scale, witness_rankBound]

theorem fixed_prescription_constraint (F : Type*) [Field F] (hK : 0 < K)
    (allocation : Allocation) {slack : ℝ} (hslack : 0 < slack)
    (hslots : ∀ slot : Slot K, slack ≤ (denominator (K := K) allocation : ℝ) *
      capacity allocation slot) :
    yieldRate (K := K) allocation slack + (Arithmetic.omega F / 3) *
      AllFieldTerminalRates.S ≤ 8 * Real.log 7 := by
  obtain ⟨W, scale, h⟩ := exists_family F hK allocation hslack hslots
  exact AllFieldRateLimit.inequality_of_rates h

theorem fixed_allocation_constraint (F : Type*) [Field F] (hK : 0 < K)
    (allocation : Allocation) (hcapacity : ∀ slot : Slot K, 0 < capacity allocation slot) :
    AllFieldInitialEntropy.nativeH0 + AllFieldScheduledYield.physicalYield K allocation / K +
      (Arithmetic.omega F / 3) * AllFieldTerminalRates.S ≤ 8 * Real.log 7 := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨slack, hslack, hslots, hloss⟩ :=
    exists_slack_for_loss hK allocation hcapacity hη
  have h := fixed_prescription_constraint F hK allocation hslack hslots
  unfold yieldRate at h
  linarith

end MatrixMultiplication.AllFieldConstructionFamily

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldOrderedLimits

open AllFieldHistory AllFieldNativeCapacity AllFieldScheduledYield
open AllFieldConstructionRates Filter
open scoped Topology

variable (F : Type*) [Field F]

theorem fixed_lot_constraint (K : ℕ) (hK : 2 ≤ K)
    (hgap : nativeB < nativeHigh)
    (hfeas : ∀ i, nativeCstar - (nativeLA i + nativeLB i) < nativeHigh)
    (ha : ∀ i, 0 < nativeLA i) (hb : ∀ i, 0 < nativeLB i)
    (hc : ∀ i, 0 < nativeLC nativeLambda i) :
    AllFieldInitialEntropy.nativeH0 + nativeCstar - nativeBeta / (K : ℝ) +
      (Arithmetic.omega F / 3) * AllFieldTerminalRates.S ≤ 8 * Real.log 7 := by
  obtain ⟨allocation, halloc⟩ := exists_balanced_allocation_sequence hgap hfeas
  have hcap := eventually_capacity_pos hK allocation halloc ha hb hc
  have hy := (physicalYield_tendsto_balanced K hK hgap allocation halloc).div_const (K : ℝ)
  have hH0 : Tendsto (fun _ : ℕ => AllFieldInitialEntropy.nativeH0) atTop
      (𝓝 AllFieldInitialEntropy.nativeH0) := tendsto_const_nhds
  have hlimit := (hH0.add hy).add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      (Arithmetic.omega F / 3) * AllFieldTerminalRates.S) atTop (𝓝 _))
  have hineq : AllFieldInitialEntropy.nativeH0 +
      ((K : ℝ) * nativeCstar - nativeBeta) / (K : ℝ) +
      (Arithmetic.omega F / 3) * AllFieldTerminalRates.S ≤ 8 * Real.log 7 := by
    apply le_of_tendsto_of_tendsto hlimit tendsto_const_nhds
    filter_upwards [hcap] with j hj
    exact AllFieldConstructionFamily.fixed_allocation_constraint F (by omega)
      (allocation j) hj
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have heq : ((K : ℝ) * nativeCstar - nativeBeta) / (K : ℝ) =
      nativeCstar - nativeBeta / (K : ℝ) := by
    rw [sub_div, mul_div_cancel_left₀ _ hk]
  rw [heq] at hineq
  linarith

theorem native_rank_constraint
    (hgap : nativeB < nativeHigh)
    (hfeas : ∀ i, nativeCstar - (nativeLA i + nativeLB i) < nativeHigh)
    (ha : ∀ i, 0 < nativeLA i) (hb : ∀ i, 0 < nativeLB i)
    (hc : ∀ i, 0 < nativeLC nativeLambda i) :
    AllFieldInitialEntropy.nativeH0 + nativeCstar +
      (Arithmetic.omega F / 3) * AllFieldTerminalRates.S ≤ 8 * Real.log 7 := by
  have hfixed (K : ℕ) (hK : 2 ≤ K) :
      (AllFieldInitialEntropy.nativeH0 + nativeCstar) - nativeBeta / (K : ℝ) +
        Arithmetic.omega F * AllFieldTerminalRates.S / 3 ≤ 8 * Real.log 7 := by
    have h := fixed_lot_constraint F K hK hgap hfeas ha hb hc
    nlinarith
  have h := FiniteSchedule.fixed_lot_boundary_limit hfixed
  nlinarith

theorem omega_le_native_ratio
    (hgap : nativeB < nativeHigh)
    (hfeas : ∀ i, nativeCstar - (nativeLA i + nativeLB i) < nativeHigh)
    (ha : ∀ i, 0 < nativeLA i) (hb : ∀ i, 0 < nativeLB i)
    (hc : ∀ i, 0 < nativeLC nativeLambda i)
    (hS : 0 < AllFieldTerminalRates.S) :
    Arithmetic.omega F ≤
      3 * (8 * Real.log 7 -
        (AllFieldInitialEntropy.nativeH0 + nativeCstar)) / AllFieldTerminalRates.S := by
  apply (le_div_iff₀ hS).mpr
  have h := native_rank_constraint F hgap hfeas ha hb hc
  nlinarith

end MatrixMultiplication.AllFieldOrderedLimits

end
end

end MatrixAllFields

end OAI
