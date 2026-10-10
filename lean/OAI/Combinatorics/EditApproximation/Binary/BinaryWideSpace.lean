import OAI.Combinatorics.EditApproximation.Binary.BinaryGridSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryOptimizerSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



theorem balancedCutAllocation_le_work (lo width M i : ℕ) :
    balancedCutAllocation lo width M i ≤ (balancedCutWithWork lo width M i).2 := by
  have hm := binaryNaturalMulAllocation_le_work i width
  have hd := binaryNaturalDivAllocation_le_work (bitWordValue (binaryNaturalMulWithWork i width).1) M
  have ha := binaryNaturalAddAllocation_le_work lo
    (bitWordValue (binaryNaturalDivModWithWork (bitWordValue (binaryNaturalMulWithWork i width).1) M).1)
  unfold balancedCutAllocation balancedCutWithWork
  dsimp only
  omega



theorem sourceChildAllocation_le_work {n M : ℕ} (parent : TargetInterval n) (i : Fin M) :
    sourceChildAllocation parent i ≤ (sourceChildWithWork parent i).2 := by
  have hw := saturatingSubtractAllocation_le_work parent.hi parent.lo
  have hn := binaryNaturalAddAllocation_le_work i.val 1
  have hl := balancedCutAllocation_le_work parent.lo
    (bitWordValue (saturatingSubtractWithWork parent.hi parent.lo).1) M i.val
  have hr := balancedCutAllocation_le_work parent.lo
    (bitWordValue (saturatingSubtractWithWork parent.hi parent.lo).1) M
    (bitWordValue (binaryNaturalAddWithWork i.val 1).1)
  unfold sourceChildAllocation sourceChildWithWork
  dsimp only
  omega



theorem seedGridSpacingAllocation_le_work (b P : ℕ) :
    seedGridSpacingAllocation b P ≤ (seedGridSpacingWithWork b P).2 := by
  have hd := binaryNaturalDivAllocation_le_work b P
  have hl := naturalWordLEAllocation_le_work (binaryNaturalDivModWithWork b P).1 [true]
  unfold seedGridSpacingAllocation seedGridSpacingWithWork
  dsimp only
  omega



theorem wideChildGridAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (i : Fin M) :
    wideChildGridAllocation parent r b P i ≤ (wideChildGridWithWork parent r b P i).2 := by
  let child := (sourceChildWithWork parent i).1
  let spacing := (seedGridSpacingWithWork b P).1
  let radius := (binaryNaturalMulWithWork 10 b).1
  let leftOffset := (saturatingSubtractWithWork child.lo parent.lo).1
  let rightOffset := (saturatingSubtractWithWork child.hi parent.lo).1
  let left := (binaryNaturalAddWithWork r.lo (bitWordValue leftOffset)).1
  let right := (binaryNaturalAddWithWork r.lo (bitWordValue rightOffset)).1
  have h1 := sourceChildAllocation_le_work parent i
  have h2 := seedGridSpacingAllocation_le_work b P
  have h3 := binaryNaturalMulAllocation_le_work 10 b
  have h4 := saturatingSubtractAllocation_le_work child.lo parent.lo
  have h5 := saturatingSubtractAllocation_le_work child.hi parent.lo
  have h6 := binaryNaturalAddAllocation_le_work r.lo (bitWordValue leftOffset)
  have h7 := binaryNaturalAddAllocation_le_work r.lo (bitWordValue rightOffset)
  have h8 := gridStateBoxAllocation_le_work ny (bitWordValue spacing) (bitWordValue radius)
    (bitWordValue left) (bitWordValue right)
  unfold wideChildGridAllocation wideChildGridWithWork
  dsimp only [child, spacing, radius, leftOffset, rightOffset, left, right] at h4 h5 h6 h7 h8 ⊢
  omega

/-- Allocations of every prefix Cartesian product, including the actual
output vector cells and the nested map/concatenation spines. -/


theorem materializedAssignmentsAllocation_le_work {α : Type*} (M : ℕ) (choices : Fin M → List α) :
    materializedAssignmentsAllocation M choices ≤ (materializedAssignmentsWithWork M choices).2 := by
  induction M with
  | zero => rfl
  | succ M ih =>
    let previous := (materializedAssignmentsWithWork M (fun i => choices i.succ)).1
    let build := fun head => arithmeticMapWithWork (fun tail : Vector α M =>
      (Vector.ofFn (Fin.cons head tail.get), 3 * (M + 1))) previous
    have hp := ih (fun i => choices i.succ)
    have hm := arithmeticFlatMapAllocation_le_work build
      (fun _ => arithmeticMapAllocation (fun _ : Vector α M => M + 1) previous) (choices 0) (by
        intro head _
        exact arithmeticMapAllocation_le_work _ _ previous (fun _ _ => by dsimp only; omega))
    change materializedAssignmentsAllocation M (fun i => choices i.succ) +
      arithmeticFlatMapAllocation build
        (fun _ => arithmeticMapAllocation (fun _ : Vector α M => M + 1) previous) (choices 0) ≤
      (materializedAssignmentsWithWork M (fun i => choices i.succ)).2 +
        (arithmeticFlatMapWithWork build (choices 0)).2 + 1
    omega



theorem wideActionGridAllocation_le_work {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) :
    wideActionGridAllocation M parent r b P ≤ (wideActionGridWithWork M parent r b P).2 := by
  have hc := vectorMapAllocation_le_work M (wideChildGridWithWork parent r b P)
    (wideChildGridAllocation parent r b P) (wideChildGridAllocation_le_work parent r b P)
  have hp := materializedAssignmentsAllocation_le_work M
    (vectorMapWithWork M (wideChildGridWithWork parent r b P)).1.get
  unfold wideActionGridAllocation wideActionGridWithWork
  dsimp only
  omega

end EditApproximation

end OAI
