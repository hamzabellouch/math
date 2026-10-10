import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ZeroWords
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Tensors
import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.HalfComplement
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWZeroGeometry

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section
namespace MatrixMultiplication.AllFieldZeroFinish
open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldTerminalStatisticLaws AllFieldTerminalRates AllFieldZeroWords
open CWWindowedLeaves CWCompleteStatistics CWZeroGeometry CWOrientedZero
open AllFieldFiniteFamily InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K : ℕ}

def canonicalZero (h : TerminalZero K) : Fin 3 := zeroAxis (shape h)
def canonicalSelected : TerminalZero K → Fin 3
  | .inl h => halfMaxAxis (aShape h.1.val)
  | .inr h => maxAxis (bShape h.1.val)
def physicalZero (h : TerminalZero K) : Fin 3 := (history h).2 (canonicalZero h)
def physicalSelected (h : TerminalZero K) : Fin 3 := (history h).2 (canonicalSelected h)

theorem shape_has_zero (h : TerminalZero K) : ∃ s, shape h s = 0 := by
  cases h with
  | inl h => exact not_positive_has_zero _ (aShape_not_positive h)
  | inr h => exact not_positive_has_zero _ h.1.property

theorem canonicalZero_spec (h : TerminalZero K) : shape h (canonicalZero h) = 0 :=
  zeroAxis_spec (shape h) (shape_has_zero h)

theorem canonicalSelected_spec (h : TerminalZero K) :
    shape h (canonicalSelected h) = shapeMax (shape h) := by
  cases h with
  | inl h => exact halfMaxAxis_spec _ (aShape_mem_shapes h)
  | inr h => exact maxAxis_spec _

theorem shape_total (h : TerminalZero K) : shapeTotal (shape h) = 2 * length h :=
  (currentShape_spec (history h).1).2

theorem shape_total_pos (h : TerminalZero K) : 0 < shapeTotal (shape h) := by
  rw [shape_total]
  cases h <;> norm_num [length, history, currentLength]

theorem axes_distinct (h : TerminalZero K) : canonicalZero h ≠ canonicalSelected h :=
  zero_ne_selected (shape h) _ _ (shape_total_pos h)
    (canonicalZero_spec h) (canonicalSelected_spec h)

theorem physical_axes_distinct (h : TerminalZero K) : physicalZero h ≠ physicalSelected h :=
  (history h).2.injective.ne (axes_distinct h)

theorem physical_shape (h : TerminalZero K) :
    currentPhysicalShape (history h) = placedShape (physicalZero h) (physicalSelected h)
      (shapeMax (shape h)) (shapeTotal (shape h) - shapeMax (shape h)) :=
  physicalShape_eq_placedShape (shape h) (history h).2 _ _
    (canonicalZero_spec h) (canonicalSelected_spec h) (axes_distinct h)

def nativeLaw : (h : TerminalZero K) → Fin 3 → Slot h → ℚ
  | .inl h, side => halfLaw (aShape h.1.val) side
  | .inr h, side => littleLaw (bParent h) (bShape h.1.val) side

theorem selected_law (h : TerminalZero K) (s : Slot h) :
    nativeLaw h (canonicalSelected h) s = law h s := by
  cases h with
  | inl h => exact halfLaw_at_maximum _ (aShape_mem_zeroSecond h) s
  | inr h =>
      change Fin 6 at s
      change littleLaw (bParent h) (bShape h.1.val) (maxAxis (bShape h.1.val)) s =
        statisticLaw (binaryParameter (bParent h) (bShape h.1.val)) (bWeight h) s
      rw [littleLaw_eq_statisticLaw _ _ _ (child_statistic_weight_bounded _
        (bParent_mem_positiveSecond h) _ (bShape_mem_below h) _)]
      congr 1
      apply Fin.ext
      exact maxAxis_spec _

theorem zero_law (h : TerminalZero K) (s : Slot h) :
    nativeLaw h (canonicalZero h) s =
      if statistic h (zeroWord (length h)) = s then 1 else 0 := by
  have hz := canonicalZero_spec h
  cases h with
  | inl h =>
      change PairSlot at s
      change aShape h.1.val (canonicalZero (.inl h)) = 0 at hz
      change halfLaw (aShape h.1.val) (canonicalZero (.inl h)) s =
        @ite ℚ (((0,0) : PairSlot) = s) (Classical.propDecidable _) 1 0
      rw [halfLaw_weight_zero _ (aShape_mem_shapes h) _ hz s]
      by_cases hs : s = (0,0)
      · rw [ite_eq_left hs, ite_eq_left hs.symm]
      · rw [ite_eq_right hs, ite_eq_right (Ne.symm hs)]
  | inr h =>
      change Fin 6 at s
      change bShape h.1.val (canonicalZero (.inr h)) = 0 at hz
      change littleLaw (bParent h) (bShape h.1.val) (canonicalZero (.inr h)) s =
        @ite ℚ ((0 : Fin 6) = s) (Classical.propDecidable _) 1 0
      simp only [littleLaw, hz, show (0 : ℕ) ≠ 2 from by decide, ite_false, singletonSlot]
      by_cases hs : s = 0
      · simp [hs]
      · simp [hs, Ne.symm hs]

theorem remaining_law (h : TerminalZero K) (side : Fin 3)
    (hz : side ≠ canonicalZero h) (hs : side ≠ canonicalSelected h) (s : Slot h) :
    nativeLaw h side s = law h ((AllFieldZeroWords.complement h).symm s) := by
  have hsum := selected_add_remaining (shape h) (canonicalZero h) (canonicalSelected h) side
    (canonicalZero_spec h) (canonicalSelected_spec h) (axes_distinct h) hz hs
  have he : nativeLaw h (canonicalSelected h) ((AllFieldZeroWords.complement h).symm s) =
      nativeLaw h side s := by
    cases h with
    | inl h =>
        exact halfLaw_complementary_sides _ (aShape_mem_shapes h) _ _ (Ne.symm hs)
          (hsum.trans (shape_total (.inl h))) s
    | inr h =>
        exact littleLaw_complement _ _ _ _
          (child_statistic_weight_bounded _ (bParent_mem_positiveSecond h) _ (bShape_mem_below h) _)
          (child_statistic_weight_bounded _ (bParent_mem_positiveSecond h) _ (bShape_mem_below h) _)
          (hsum.trans (shape_total (.inr h))) s
  rw [selected_law] at he
  exact he.symm

def embed (allocation : Allocation) (m : ℕ) (h : TerminalZero K)
    (side : Fin 3) (w : ZeroWords allocation m h) :
    HistoryWord allocation (terminalDilation K m) (history h) :=
  fun i => sideWord (physicalZero h) (physicalSelected h) side (words allocation m h w i)

theorem embed_window (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (h : TerminalZero K) (side : Fin 3) (η : ℝ) (hη : 0 ≤ η)
    (w : ZeroWords allocation m h) :
    typeWindow (fun s => (nativeLaw h ((history h).2.symm side) s : ℝ)) η
      (fun i => statistic h (embed allocation m h side w i)) := by
  by_cases hz : side = physicalZero h
  · have hc : (history h).2.symm side = canonicalZero h := by
      simp only [hz, physicalZero, Equiv.symm_apply_apply]
    simp only [embed, sideWord, ite_eq_left hz, hc]
    have hpop : 0 < population allocation (terminalDilation K m) (history h) := by
      rw [← statisticCounts_repeat_sum allocation m h, ← Finset.mul_sum]
      exact Nat.mul_pos hm (statisticCounts_pos allocation h)
    apply zero_window (length h) _ hpop (statistic h) _ η hη
    intro s
    rw [zero_law]
    split_ifs <;> norm_num
  · by_cases hs : side = physicalSelected h
    · have hc : (history h).2.symm side = canonicalSelected h := by
        simp only [hs, physicalSelected, Equiv.symm_apply_apply]
      simpa only [embed, sideWord, ite_eq_right hz, ite_eq_left hs, hc, selected_law] using
        selected_window allocation hm h η hη w
    · have hcz : (history h).2.symm side ≠ canonicalZero h := by
        intro hh
        apply hz
        exact ((history h).2.apply_symm_apply side).symm.trans (congrArg (history h).2 hh)
      have hcs : (history h).2.symm side ≠ canonicalSelected h := by
        intro hh
        apply hs
        exact ((history h).2.apply_symm_apply side).symm.trans (congrArg (history h).2 hh)
      have hlaw : (fun s => (nativeLaw h ((history h).2.symm side) s : ℝ)) =
          (fun s => (law h s : ℝ)) ∘ (AllFieldZeroWords.complement h).symm := by
        funext s
        exact congrArg (fun q : ℚ => (q : ℝ)) (remaining_law h _ hcz hcs s)
      have hword : (fun i => statistic h (embed allocation m h side w i)) =
          (fun i => statistic h (complementWord (words allocation m h w i).val)) := by
        funext i
        simp only [embed, sideWord, ite_eq_right hz, ite_eq_right hs]
        rfl
      rw [hlaw, hword]
      exact complementary_window allocation hm h η hη w

theorem embed_mask (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (h : TerminalZero K) (side : Fin 3)
    (w : ZeroWords allocation m h) :
    residentMask allocation (terminalDilation K m) ε (history h) side
      (embed allocation m h side w) := by
  cases h with
  | inl h =>
      intro _
      exact embed_window allocation hm (.inl h) side (ε/8) (by positivity) w
  | inr h =>
      intro _
      exact embed_window allocation hm (.inr h) side (ε/128) (by positivity) w

variable (F : Type*) [Field F]

theorem coefficient (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (h : TerminalZero K) (x y z : ZeroWords allocation m h) :
    historyTensor F allocation (terminalDilation K m) ε (history h)
      (embed allocation m h 0 x) (embed allocation m h 1 y) (embed allocation m h 2 z) =
      if matched (physicalZero h) x y z then 1 else 0 := by
  simp only [historyTensor, ExactRecovery.delete, embed_mask allocation hm hε,
    and_self, ite_true]
  rw [physical_shape]
  exact power_coefficient F (length h) _ _ _
    ((max_add_complement (shape h)).trans (shape_total h))
    (physicalZero h) (physicalSelected h) (physical_axes_distinct h)
    (words allocation m h) (words_injective allocation m h) x y z

abbrev Row (allocation : Allocation) (m : ℕ) (h : TerminalZero K) :=
  CWOrientedZero.Row (physicalZero h) (ZeroWords allocation m h)
abbrev Middle (allocation : Allocation) (m : ℕ) (h : TerminalZero K) :=
  CWOrientedZero.Middle (physicalZero h) (ZeroWords allocation m h)
abbrev Column (allocation : Allocation) (m : ℕ) (h : TerminalZero K) :=
  CWOrientedZero.Column (physicalZero h) (ZeroWords allocation m h)

def localMap (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (h : TerminalZero K) :
    LocalMap (historyTensor F allocation (terminalDilation K m) ε (history h))
      (Tensor.matrixCoefficients (Row allocation m h) (Middle allocation m h) (Column allocation m h)) := by
  letI : Nonempty (ZeroWords allocation m h) :=
    Fintype.card_pos_iff.mp (zeroWords_card_pos allocation m h)
  exact ofMatching F _ (physicalZero h) (embed allocation m h)
    (coefficient F allocation hm hε h)

theorem volume (allocation : Allocation) (m : ℕ) (h : TerminalZero K) :
    Fintype.card (Row allocation m h) * Fintype.card (Middle allocation m h) *
      Fintype.card (Column allocation m h) = Fintype.card (ZeroWords allocation m h) :=
  CWOrientedZero.volume (physicalZero h) (ZeroWords allocation m h)

theorem dimensions_pos (allocation : Allocation) (m : ℕ) (h : TerminalZero K) :
    0 < Fintype.card (Row allocation m h) ∧
      0 < Fintype.card (Middle allocation m h) ∧ 0 < Fintype.card (Column allocation m h) := by
  have hp := zeroWords_card_pos allocation m h
  rw [← volume allocation m h] at hp
  have hab := Nat.pos_of_mul_pos_right hp
  exact ⟨Nat.pos_of_mul_pos_right hab, Nat.pos_of_mul_pos_left hab,
    Nat.pos_of_mul_pos_left hp⟩

end MatrixMultiplication.AllFieldZeroFinish

end

end OAI
