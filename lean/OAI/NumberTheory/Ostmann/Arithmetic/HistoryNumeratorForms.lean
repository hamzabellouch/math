import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCoefficientBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCoefficientRegular

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryNumeratorForms
open Construction Characters.RationalHistory
open HistorySymbolicState HistorySymbolicSlots HistorySymbolicScope HistorySymbolicNumerator
open HistorySymbolicLinearity HistorySymbolicCost HistoryCoefficientRegular

variable {ι : Type*} {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

def nodeNumerator (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) : Expr ι :=
  numeratorExpr left.root.frequency right.root.frequency e.plus e.minus
    (List.ofFn (leftPart (splitSlots hs e))) (List.ofFn (rightPart (splitSlots hs e)))

theorem nodeNumerator_eval (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (x : ι → ℚ) (he : e.Correct x) :
    (nodeNumerator hs e).rationalEval x =
      (reversalNumerator left.root.frequency right.root.frequency
        ((a.giantPlus*(hp.map SmallSlot.value).prod:ℕ):ℤ)
        ((a.giantMinus*(hm.map SmallSlot.value).prod:ℕ):ℤ):ℚ) := by
  have hsplit := correct_reorder (History.supported_small_split hs) e.small he.2.2.2.2
  have hhp := product_correct _ (correct_leftPart _ hsplit)
  have hhm := product_correct _ (correct_rightPart _ hsplit)
  change (left.root.frequency:ℚ)*(e.minus.rationalEval x*_) -
    (right.root.frequency:ℚ)*(e.plus.rationalEval x*_) = _
  simp only [splitSlots]
  rw [he.2.1,he.2.2.2.1,hhp.2,hhm.2]
  simp only [reversalNumerator,Int.cast_mul,Int.cast_natCast,Nat.cast_mul]

theorem nodeNumerator_linear
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e c d : StateExpr a ι) (x : ι → ℚ) (X Y : ℚ) (he : StateLinear x X Y e c d) :
    (nodeNumerator hs e).rationalEval x =
      (nodeNumerator hs c).rationalEval x*X+(nodeNumerator hs d).rationalEval x*Y := by
  simp only [nodeNumerator,numeratorExpr,Expr.rationalEval,splitSlots,he.2.2.1,he.2.2.2]
  rw [he.1,he.2.1]
  ring

theorem nodeNumerator_regular
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (x : ι → ℚ) (he : StateRegular e x) :
    (nodeNumerator hs e).RegularAt x := by
  have hsplit := correct_reorder (History.supported_small_split hs) e.small he.2.2
  have hhp := product_correct _ (correct_leftPart _ hsplit)
  have hhm := product_correct _ (correct_rightPart _ hsplit)
  exact ⟨⟨trivial,he.2.1,hhm.1⟩,⟨trivial,he.1,hhp.1⟩⟩

theorem nodeNumerator_above
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (level : ι → ℕ) (he : StateAbove level (l+1) e) :
    Above level (l+1) (nodeNumerator hs e) := by
  apply numeratorExpr_above
  · exact he.1
  · exact he.2.1
  · intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact he.2.2 _
  · intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact he.2.2 _

theorem nodeNumerator_atomCount
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) : (nodeNumerator hs e).atomCount = stateCost e := by
  simp only [nodeNumerator,numeratorExpr,Expr.atomCount,HistorySymbolicStep.product_atomCount,
    sum_atomCount_ofFn]
  have hparts := slotCost_parts (splitSlots hs e)
  have hsplit := slotCost_reorder (History.supported_small_split hs) e.small
  change slotCost (splitSlots hs e) = slotCost e.small at hsplit
  unfold stateCost
  omega

theorem nodeNumerator_degree_le
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) :
    (nodeNumerator hs e).numerator.totalDegree ≤ stateCost e ∧
      (nodeNumerator hs e).denominator.totalDegree ≤ stateCost e := by
  simpa only [nodeNumerator_atomCount] using (nodeNumerator hs e).fraction_degree_le

end Ostmann.Arithmetic.HistoryNumeratorForms

end

end OAI
