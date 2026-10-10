import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightPivot
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicEncoding

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryProductWindows
open Construction Characters.RationalHistory HistorySymbolicSlots HistorySymbolicState
variable {ι : Type*}

def slotSum (F : SmallSlot → Expr ι → ℝ) (xs : List SmallSlot)
    (f : Fin xs.length → Expr ι) : ℝ := ∑i,F (xs.get i) (f i)

theorem slotSum_reorder (F : SmallSlot → Expr ι → ℝ) {xs ys : List SmallSlot}
    (h : xs.Perm ys) (f : Fin xs.length → Expr ι) :
    slotSum F ys (reorder h f) = slotSum F xs f := by
  unfold slotSum
  rw [←(OccurrencePermutation.indexEquiv h).sum_comp]
  simp only [reorder, Equiv.symm_apply_apply, OccurrencePermutation.get_indexEquiv]

theorem slotSum_parts (F : SmallSlot → Expr ι → ℝ) {xs ys : List SmallSlot}
    (f : Fin (xs++ys).length → Expr ι) :
    slotSum F (xs++ys) f = slotSum F xs (leftPart f) + slotSum F ys (rightPart f) := by
  unfold slotSum
  rw [←(finCongr (List.length_append (as := xs) (bs := ys))).symm.sum_comp]
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    change F ((xs++ys).get (leftIndex xs ys i)) (f (leftIndex xs ys i)) = _
    rw [get_leftIndex]
    rfl
  · apply Finset.sum_congr rfl
    intro i _
    change F ((xs++ys).get (rightIndex xs ys i)) (f (rightIndex xs ys i)) = _
    rw [get_rightIndex]
    rfl

theorem slotSum_append (F : SmallSlot → Expr ι → ℝ) {xs ys : List SmallSlot}
    (f : Fin xs.length → Expr ι) (g : Fin ys.length → Expr ι) :
    slotSum F (xs++ys) (append f g) = slotSum F xs f + slotSum F ys g := by
  rw [slotSum_parts]
  have hl : leftPart (append f g) = f := by
    funext i
    change Fin.append f g (Fin.castAdd ys.length i) = f i
    exact Fin.append_left _ _ _
  have hr : rightPart (append f g) = g := by
    funext i
    change Fin.append f g (Fin.natAdd xs.length i) = g i
    exact Fin.append_right _ _ _
  rw [hl,hr]

def bulkLog (xs : List SmallSlot) (f : Fin xs.length → Expr ι) (x : ι → ℝ) : ℝ :=
  slotSum (fun q e => if q.role = .bulk then Real.log (e.realEval x) else 0) xs f

theorem bulkLog_compensation (j : ℕ) (u : List SmallSlot)
    (hu : ∀q∈u,q.role = .compensation j) (f : Fin u.length → Expr ι) (x : ι → ℝ) :
    bulkLog u f x = 0 := by
  unfold bulkLog slotSum
  apply Finset.sum_eq_zero
  intro i _
  dsimp only
  rw [hu (u.get i) (List.get_mem u i)]
  simp

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

theorem bulkLog_children (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) (x : ι → ℝ) :
    bulkLog left.root.small (leftState hs e comp).small x =
      bulkLog hp (leftPart (splitSlots hs e)) x ∧
    bulkLog right.root.small (rightState hs e comp).small x =
      bulkLog hm (rightPart (splitSlots hs e)) x := by
  have hz := bulkLog_compensation (l+1) u (History.supported_compensation_roles hs) comp x
  constructor
  · simp only [bulkLog, leftState, slotSum_reorder, slotSum_append]
    change bulkLog u comp x + _ = _
    rw [hz,zero_add]
  · simp only [bulkLog, rightState, slotSum_reorder, slotSum_append]
    change bulkLog u comp x + _ = _
    rw [hz,zero_add]

theorem bulkLog_node (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) (x : ι → ℝ) :
    bulkLog a.small e.small x = bulkLog left.root.small (leftState hs e comp).small x +
      bulkLog right.root.small (rightState hs e comp).small x := by
  rw [(bulkLog_children hs e comp x).1, (bulkLog_children hs e comp x).2]
  unfold bulkLog
  rw [←slotSum_parts]
  exact (slotSum_reorder _ (History.supported_small_split hs) e.small).symm

end Ostmann.Arithmetic.HistoryProductWindows

end

end OAI
