import OAI.NumberTheory.Ostmann.Tree.CycleQuartets
import OAI.NumberTheory.Ostmann.Tree.QuartetActions
import OAI.NumberTheory.Ostmann.Tree.QuartetFactorizationLeaves

namespace OAI

noncomputable section
namespace Ostmann.Tree.CycleQuartet
open QuartetFactorization Density

def leaf : (k : ℕ) → Leaves k → Leaves 2 → Leaves (k+2)
  | 0,_,w => w
  | k+1,v,w => Fin.cons (v 0) (leaf k (Fin.tail v) w)

def tail : (k : ℕ) → Leaves (k+2) → Leaves 2
  | 0,e => e
  | k+1,e => tail k (Fin.tail e)

@[simp] theorem tail_leaf (k : ℕ) (v : Leaves k) (w : Leaves 2) :
    tail k (leaf k v w)=w := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [tail,leaf,Fin.tail_cons,ih]

@[simp] theorem label_leaf (k : ℕ) (v : Leaves k) (w : Leaves 2) :
    (bottomCut k).label (leaf k v w)=v := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    cases hv : v 0 <;>
      simp only [bottomCut,leaf,hv,Cut.label_cons_false,Cut.label_cons_true,ih]
    · simpa only [hv] using Fin.cons_self_tail v
    · simpa only [hv] using Fin.cons_self_tail v

@[simp] theorem leaf_label_tail (k : ℕ) (e : Leaves (k+2)) :
    leaf k ((bottomCut k).label e) (tail k e)=e := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases he : e 0 <;>
      simp only [bottomCut,Cut.label,he,Bool.false_eq_true,↓reduceIte,leaf,
        Fin.cons_zero,Fin.tail_cons,tail,ih]
    · simpa only [he] using Fin.cons_self_tail e
    · simpa only [he] using Fin.cons_self_tail e

theorem leaf_injective (k : ℕ) (v : Leaves k) : Function.Injective (leaf k v) := by
  intro a b h
  simpa only [tail_leaf] using congrArg (tail k) h

@[simp] theorem quartetCut_label_leaf (k : ℕ) (v : Leaves k) (w : Leaves 2) :
    (quartetCut k).label (leaf k v w)=v := by
  rw [show quartetCut k=bottomCut k from cut_unique _ _]
  exact label_leaf k v w

@[simp] theorem leaf_quartetCut_label_tail (k : ℕ) (e : Leaves (k+2)) :
    leaf k ((quartetCut k).label e) (tail k e)=e := by
  rw [show quartetCut k=bottomCut k from cut_unique _ _]
  exact leaf_label_tail k e

theorem bottomLeaves_apply {F : Type*} [Field F] (k : ℕ)
    (M : Leaves (k+2) → Fˣ) (v : Leaves k) (w : Leaves 2) :
    bottomLeaves k M v w=M (leaf k v w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases hv : v 0 <;>
      simp only [bottomLeaves,join,hv,Bool.false_eq_true,↓reduceIte,leaf,ih,left,right]

end Ostmann.Tree.CycleQuartet

end

end OAI
