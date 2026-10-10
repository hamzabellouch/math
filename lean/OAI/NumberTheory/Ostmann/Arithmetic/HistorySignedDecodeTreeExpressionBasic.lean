import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeExpression

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedDecode
open Construction Characters.RationalHistory HistorySymbolicSlots HistorySymbolicState HistorySymbolicStep
variable {ι : Type*}

def SmallRealValues (x : ι → ℝ) (xs : List SmallSlot)
    (f : Fin xs.length → Expr ι) : Prop :=
  ∀ i, (f i).realEval x = ((xs.get i).value : ℝ)

theorem smallRealValues_reorder {x : ι → ℝ} {xs ys : List SmallSlot}
    (h : xs.Perm ys) (f : Fin xs.length → Expr ι) (hf : SmallRealValues x xs f) :
    SmallRealValues x ys (reorder h f) := by
  intro i
  have he := OccurrencePermutation.get_indexEquiv h ((OccurrencePermutation.indexEquiv h).symm i)
  simp only [Equiv.apply_symm_apply] at he
  exact (hf _).trans (congrArg (fun q : SmallSlot => (q.value : ℝ)) he.symm)

theorem smallRealValues_leftPart {x : ι → ℝ} {xs ys : List SmallSlot}
    (f : Fin (xs ++ ys).length → Expr ι) (hf : SmallRealValues x (xs ++ ys) f) :
    SmallRealValues x xs (leftPart f) := by
  intro i
  simpa only [leftPart, get_leftIndex] using hf (leftIndex xs ys i)

theorem smallRealValues_rightPart {x : ι → ℝ} {xs ys : List SmallSlot}
    (f : Fin (xs ++ ys).length → Expr ι) (hf : SmallRealValues x (xs ++ ys) f) :
    SmallRealValues x ys (rightPart f) := by
  intro i
  simpa only [rightPart, get_rightIndex] using hf (rightIndex xs ys i)

theorem smallRealValues_append {x : ι → ℝ} {xs ys : List SmallSlot}
    (f : Fin xs.length → Expr ι) (g : Fin ys.length → Expr ι)
    (hf : SmallRealValues x xs f) (hg : SmallRealValues x ys g) :
    SmallRealValues x (xs ++ ys) (append f g) := by
  intro i
  let j : Fin (xs.length + ys.length) :=
    Fin.cast (show (xs ++ ys).length = xs.length + ys.length from List.length_append) i
  change (Fin.append f g j).realEval x = ((xs ++ ys).get i).value
  have hj : Fin.cast (show (xs ++ ys).length = xs.length + ys.length from
      List.length_append).symm j = i := by simp [j]
  rw [← hj]
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simpa [Fin.append_left, leftIndex] using hf k
  · simpa [Fin.append_right, rightIndex] using hg k

theorem smallRealValues_product {x : ι → ℝ} {xs : List SmallSlot}
    (f : Fin xs.length → Expr ι) (hf : SmallRealValues x xs f) :
    (product (List.ofFn f)).realEval x = ((xs.map SmallSlot.value).prod : ℝ) := by
  rw [product_realEval, List.map_ofFn]
  have hv : (fun i => (f i).realEval x) = (fun i => ((xs.get i).value : ℝ)) := funext hf
  simp only [Function.comp_def]
  rw [hv]
  calc
    _ = (xs.map (fun q => (q.value : ℝ))).prod :=
      congrArg List.prod (List.ofFn_getElem_eq_map xs (fun q => (q.value : ℝ)))
    _ = _ := by simp only [Nat.cast_list_prod, List.map_map, Function.comp_def]

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

theorem children_smallRealValues
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) (x : ι → ℝ)
    (he : SmallRealValues x a.small e.small) (hc : SmallRealValues x u comp) :
    SmallRealValues x left.root.small (leftState hs e comp).small ∧
      SmallRealValues x right.root.small (rightState hs e comp).small := by
  have hsplit := smallRealValues_reorder (History.supported_small_split hs) e.small he
  exact ⟨smallRealValues_reorder (History.supported_child_small hs).1.symm _
      (smallRealValues_append comp _ hc (smallRealValues_leftPart _ hsplit)),
    smallRealValues_reorder (History.supported_child_small hs).2.symm _
      (smallRealValues_append comp _ hc (smallRealValues_rightPart _ hsplit))⟩

theorem pivotExpr_realEval_eq_signedPivot
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) (x : ι → ℝ) (Xp Xm : ℤ)
    (heplus : e.plus.realEval x = (Xp : ℝ)) (heminus : e.minus.realEval x = (Xm : ℝ))
    (he : SmallRealValues x a.small e.small) (hc : SmallRealValues x u comp)
    (hden : a.frequency * ((u.map SmallSlot.value).prod : ℤ) ≠ 0)
    (hd : a.frequency * ((u.map SmallSlot.value).prod : ℤ) ∣
      reversalNumerator left.root.frequency right.root.frequency
        (Xp * ((hp.map SmallSlot.value).prod : ℤ))
        (Xm * ((hm.map SmallSlot.value).prod : ℤ))) :
    (pivotExpr hs e comp).realEval x =
      (signedPivot ⟨a.frequency, Xp, Xm, a.small⟩ left.root.frequency right.root.frequency
        u hp hm : ℝ) := by
  have hsplit := smallRealValues_reorder (History.supported_small_split hs) e.small he
  exact pivot_realEval_eq_signedPivot ⟨a.frequency, Xp, Xm, a.small⟩
    left.root.frequency right.root.frequency u hp hm hden hd e.plus e.minus
    (List.ofFn comp) (List.ofFn (leftPart (splitSlots hs e)))
    (List.ofFn (rightPart (splitSlots hs e))) x heplus heminus
    (smallRealValues_product comp hc)
    (smallRealValues_product _ (smallRealValues_leftPart _ hsplit))
    (smallRealValues_product _ (smallRealValues_rightPart _ hsplit))

end Ostmann.Arithmetic.HistorySignedDecode

end

end OAI
