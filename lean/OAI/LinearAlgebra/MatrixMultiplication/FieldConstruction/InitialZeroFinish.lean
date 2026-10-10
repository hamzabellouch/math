import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWZeroGeometry
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Tensors
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.InitialLeafRates
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.Terminal

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

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

end OAI
