import Mathlib
import OAI.LinearAlgebra.MatrixFields.Histories.HistoryChildLaws

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldTerminalStatisticLaws

open AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev AZero (K : ℕ) :=
  {h : AfterA K // aShape h ∉ positiveSecond} × Placement

abbrev BZero (K : ℕ) :=
  {h : AfterB K // positive (bShape h) ≠ true} × Placement

abbrev TerminalZero (K : ℕ) := AZero K ⊕ BZero K

variable {K : ℕ}

theorem aShape_mem_shapes (h : AZero K) : aShape h.1.val ∈ shapes 8 :=
  aShape_size h.1.val

theorem aShape_not_positive (h : AZero K) : positive (aShape h.1.val) ≠ true := by
  intro hp
  exact h.1.property (List.mem_filter.mpr ⟨aShape_mem_shapes h, hp⟩)

theorem aShape_mem_zeroSecond (h : AZero K) : aShape h.1.val ∈ zeroSecond := by
  simp [zeroSecond, aShape_mem_shapes h, aShape_not_positive h]

def bParent (h : BZero K) : Shape := aShape h.1.val.1.val

theorem bParent_mem_positiveSecond (h : BZero K) : bParent h ∈ positiveSecond :=
  h.1.val.1.property

theorem bShape_mem_shapes (h : BZero K) : bShape h.1.val ∈ shapes 4 :=
  bShape_size h.1.val

theorem bShape_mem_below (h : BZero K) : bShape h.1.val ∈ below (bParent h) :=
  bShape_mem h.1.val

theorem bShape_max_lt_five (h : BZero K) : shapeMax (bShape h.1.val) < 5 := by
  have hb := child_statistic_weight_bounded (bParent h)
    (bParent_mem_positiveSecond h) (bShape h.1.val) (bShape_mem_below h)
  exact max_lt_iff.mpr ⟨hb 0, max_lt_iff.mpr ⟨hb 1, hb 2⟩⟩

def bWeight (h : BZero K) : Fin 5 :=
  ⟨shapeMax (bShape h.1.val), bShape_max_lt_five h⟩

@[simp] theorem bWeight_val (h : BZero K) : (bWeight h).val = shapeMax (bShape h.1.val) :=
  rfl

def Slot : TerminalZero K → Type
  | .inl _ => PairSlot
  | .inr _ => Fin 6

instance (h : TerminalZero K) : Fintype (Slot h) := by
  cases h <;> dsimp [Slot] <;> infer_instance

def history : TerminalZero K → History K
  | .inl h => (.afterA h.1.val, h.2)
  | .inr h => (.afterB h.1.val, h.2)

@[simp] theorem history_inl (h : AZero K) :
    history (.inl h) = (.afterA h.1.val, h.2) := rfl

@[simp] theorem history_inr (h : BZero K) :
    history (.inr h) = (.afterB h.1.val, h.2) := rfl

def law : (h : TerminalZero K) → Slot h → ℚ
  | .inl h, s => zeroPairLaw (aShape h.1.val) s.1 s.2
  | .inr h, s => statisticLaw (binaryParameter (bParent h) (bShape h.1.val)) (bWeight h) s

@[simp] theorem law_inl (h : AZero K) (s : PairSlot) :
    law (.inl h) s = zeroPairLaw (aShape h.1.val) s.1 s.2 := rfl

@[simp] theorem law_inr (h : BZero K) (s : Fin 6) :
    law (.inr h) s =
      statisticLaw (binaryParameter (bParent h) (bShape h.1.val)) (bWeight h) s := rfl

theorem statisticLaw_nonnegative (t u : Shape) (k : Fin 5) (s : Fin 6) :
    0 ≤ statisticLaw (binaryParameter t u) k s := by
  obtain ⟨hl, hh⟩ := binaryParameter_bounds t u
  unfold statisticLaw
  split_ifs <;> linarith

theorem statisticLaw_total (d : ℚ) (k : Fin 5) :
    ∑ s : Fin 6, statisticLaw d k s = 1 := by
  fin_cases k <;> simp [statisticLaw, Fin.sum_univ_succ, singletonSlot]

theorem law_nonneg (h : TerminalZero K) (s : Slot h) : 0 ≤ law h s := by
  cases h with
  | inl h => exact zeroPairLaw_nonnegative (aShape h.1.val) s.1 s.2
  | inr h => exact statisticLaw_nonnegative (bParent h) (bShape h.1.val) (bWeight h) s

theorem law_total (h : TerminalZero K) : ∑ s : Slot h, law h s = 1 := by
  cases h with
  | inl h => exact zeroPairLaw_full_normalized (aShape h.1.val) (aShape_mem_zeroSecond h)
  | inr h => exact statisticLaw_total _ (bWeight h)

theorem history_amount_pos (allocation : Allocation) (h : TerminalZero K) :
    0 < amount allocation (history h) := by
  cases h with
  | inl h =>
      change 0 < aAmount h.1.val / 6
      exact div_pos (aAmount_pos h.1.val) (by norm_num)
  | inr h =>
      change 0 < bAmount h.1.val / 6
      exact div_pos (bAmount_pos h.1.val) (by norm_num)

end MatrixMultiplication.AllFieldTerminalStatisticLaws

end
end

end MatrixAllFields

end OAI
