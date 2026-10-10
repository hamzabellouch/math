import OAI.Combinatorics.EditApproximation.Binary.BinaryScaleGrid
import OAI.Combinatorics.EditApproximation.Binary.BinaryGradientWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Actual wide-action materialization starts from binary balanced cuts and
bounded endpoint grids. The Cartesian-product routine receives the lists
just computed, so their construction is included in the counter. -/

namespace EditApproximation



@[simp] theorem balancedCutWithWork_value (lo width M i : ℕ) (hM : 0 < M) :
    bitWordValue (balancedCutWithWork lo width M i).1 = balancedCut lo width M i := by
  simp only [balancedCutWithWork, binaryNaturalAddWithWork_value,
    (binaryNaturalDivModWithWork_spec _ M hM).1, binaryNaturalMulWithWork_value, balancedCut]



@[simp] theorem sourceChildWithWork_value {n M : ℕ} (parent : TargetInterval n) (i : Fin M) :
    (sourceChildWithWork parent i).1 = sourceChild parent i := by
  have hl : (sourceChildWithWork parent i).1.lo = (sourceChild parent i).lo := by
    simp only [sourceChildWithWork, balancedCutWithWork_value _ _ _ _ (Nat.zero_lt_of_lt i.isLt),
      saturatingSubtractWithWork_value, sourceChild]
  have hh : (sourceChildWithWork parent i).1.hi = (sourceChild parent i).hi := by
    simp only [sourceChildWithWork, balancedCutWithWork_value _ _ _ _ (Nat.zero_lt_of_lt i.isLt),
      saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value, sourceChild]
  generalize heq : (sourceChildWithWork parent i).1 = first at hl hh ⊢
  generalize hother : sourceChild parent i = second at hl hh ⊢
  cases first
  cases second
  cases hl
  cases hh
  rfl



@[simp] theorem wideChildGridWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (i : Fin M) (hP : 0 < P) :
    (wideChildGridWithWork parent r b P i).1 = wideChildStateList parent r b P i := by
  simp only [wideChildGridWithWork, sourceChildWithWork_value,
    seedGridSpacingWithWork_value b P hP, binaryNaturalMulWithWork_value,
    saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value, wideChildStateList]
  apply gridStateBoxWithWork_value
  unfold seedGridSpacing
  omega



@[simp] theorem wideActionGridWithWork_value {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (hP : 0 < P) :
    ((wideActionGridWithWork M parent r b P).1.map Vector.get) = wideActionList M parent r b P := by
  have hchoices : (vectorMapWithWork M (wideChildGridWithWork parent r b P)).1.get =
      wideChildStateList parent r b P := by
    funext i
    rw [vectorMapWithWork_value, wideChildGridWithWork_value _ _ _ _ _ hP]
  simp only [wideActionGridWithWork, materializedAssignmentsWithWork_value, hchoices, wideActionList]

theorem wideActionGridWithWork_cost {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P C : ℕ) (hP : 0 < P)
    (hc : ∀ i : Fin M, (wideChildGridWithWork parent r b P i).2 ≤ C) :
    (wideActionGridWithWork M parent r b P).2 ≤
      M * (C + 6) + (M + 1) * (6 * M + 10) * ((40 * P + 2) ^ 2 + 1) ^ (M + 1) + 1 := by
  let choices := vectorMapWithWork M (wideChildGridWithWork parent r b P)
  have hm := BinaryFraction.vectorMapWithWork_cost_le M (wideChildGridWithWork parent r b P) C hc
  have hchoice (i : Fin M) : (choices.1.get i).length ≤ (40 * P + 2) ^ 2 := by
    simp only [choices, vectorMapWithWork_value, wideChildGridWithWork_value _ _ _ _ _ hP]
    exact wideChildStateList_length_le parent r hP i
  have hp := materializedAssignmentsWithWork_cost M ((40 * P + 2) ^ 2) choices.1.get hchoice
  change choices.2 ≤ _ at hm
  change choices.2 + (materializedAssignmentsWithWork M choices.1.get).2 + 1 ≤ _
  omega

end EditApproximation

end OAI
