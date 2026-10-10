import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicStep
import OAI.NumberTheory.Ostmann.Arithmetic.OccurrencePermutation

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicSlots
open Construction Characters.RationalHistory

variable {ι : Type*}

def Correct (x : ι → ℚ) (xs : List SmallSlot) (f : Fin xs.length → Expr ι) : Prop :=
  ∀ i, (f i).RegularAt x ∧ (f i).rationalEval x = ((xs.get i).value:ℚ)

def reorder {xs ys : List SmallSlot} (h : xs.Perm ys) (f : Fin xs.length → Expr ι) :
    Fin ys.length → Expr ι := fun i => f ((OccurrencePermutation.indexEquiv h).symm i)

theorem correct_reorder {x : ι → ℚ} {xs ys : List SmallSlot} (h : xs.Perm ys)
    (f : Fin xs.length → Expr ι) (hf : Correct x xs f) : Correct x ys (reorder h f) := by
  intro i
  have he := OccurrencePermutation.get_indexEquiv h ((OccurrencePermutation.indexEquiv h).symm i)
  simp only [Equiv.apply_symm_apply] at he
  exact ⟨(hf _).1,(hf _).2.trans (congrArg (fun q : SmallSlot => (q.value:ℚ)) he.symm)⟩

def leftIndex (xs ys : List SmallSlot) (i : Fin xs.length) : Fin (xs++ys).length :=
  ⟨i.val,by simp only [List.length_append]; omega⟩

def rightIndex (xs ys : List SmallSlot) (i : Fin ys.length) : Fin (xs++ys).length :=
  ⟨xs.length+i.val,by simp only [List.length_append]; omega⟩

@[simp] theorem get_leftIndex (xs ys : List SmallSlot) (i : Fin xs.length) :
    (xs++ys).get (leftIndex xs ys i) = xs.get i := by
  simp [leftIndex,List.getElem_append_left]

@[simp] theorem get_rightIndex (xs ys : List SmallSlot) (i : Fin ys.length) :
    (xs++ys).get (rightIndex xs ys i) = ys.get i := by
  simp [rightIndex,List.getElem_append_right]

def leftPart {xs ys : List SmallSlot} (f : Fin (xs++ys).length → Expr ι) :
    Fin xs.length → Expr ι := fun i => f (leftIndex xs ys i)

def rightPart {xs ys : List SmallSlot} (f : Fin (xs++ys).length → Expr ι) :
    Fin ys.length → Expr ι := fun i => f (rightIndex xs ys i)

theorem correct_leftPart {x : ι → ℚ} {xs ys : List SmallSlot}
    (f : Fin (xs++ys).length → Expr ι) (hf : Correct x (xs++ys) f) :
    Correct x xs (leftPart f) := by
  intro i
  simpa only [leftPart,get_leftIndex] using hf (leftIndex xs ys i)

theorem correct_rightPart {x : ι → ℚ} {xs ys : List SmallSlot}
    (f : Fin (xs++ys).length → Expr ι) (hf : Correct x (xs++ys) f) :
    Correct x ys (rightPart f) := by
  intro i
  simpa only [rightPart,get_rightIndex] using hf (rightIndex xs ys i)

def append {xs ys : List SmallSlot} (f : Fin xs.length → Expr ι) (g : Fin ys.length → Expr ι) :
    Fin (xs++ys).length → Expr ι := fun i =>
      Fin.append f g (Fin.cast (show (xs++ys).length = xs.length+ys.length from List.length_append) i)

theorem correct_append {x : ι → ℚ} {xs ys : List SmallSlot}
    (f : Fin xs.length → Expr ι) (g : Fin ys.length → Expr ι)
    (hf : Correct x xs f) (hg : Correct x ys g) : Correct x (xs++ys) (append f g) := by
  intro i
  let j : Fin (xs.length+ys.length) := Fin.cast (show (xs++ys).length = xs.length+ys.length from List.length_append) i
  change (Fin.append f g j).RegularAt x ∧
    (Fin.append f g j).rationalEval x = ((xs++ys).get i).value
  have hj : Fin.cast (show (xs++ys).length = xs.length+ys.length from List.length_append).symm j = i := by simp [j]
  rw [← hj]
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simpa [Fin.append_left,leftIndex] using hf k
  · simpa [Fin.append_right,rightIndex] using hg k

theorem product_correct {x : ι → ℚ} {xs : List SmallSlot}
    (f : Fin xs.length → Expr ι) (hf : Correct x xs f) :
    (HistorySymbolicStep.product (List.ofFn f)).RegularAt x ∧
    (HistorySymbolicStep.product (List.ofFn f)).rationalEval x =
      ((xs.map SmallSlot.value).prod:ℚ) := by
  refine ⟨HistorySymbolicStep.product_regular _ _ ?_,?_⟩
  · intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact (hf i).1
  · rw [HistorySymbolicStep.product_eval, List.map_ofFn]
    have hv : (fun i => (f i).rationalEval x) =
        (fun i => ((xs.get i).value:ℚ)) := funext (fun i => (hf i).2)
    simp only [Function.comp_def]
    rw [hv]
    calc
      _ = (xs.map (fun q => (q.value:ℚ))).prod :=
        congrArg List.prod (List.ofFn_getElem_eq_map xs (fun q => (q.value:ℚ)))
      _ = _ := by simp only [Nat.cast_list_prod,List.map_map,Function.comp_def]

end Ostmann.Arithmetic.HistorySymbolicSlots

end

end OAI
