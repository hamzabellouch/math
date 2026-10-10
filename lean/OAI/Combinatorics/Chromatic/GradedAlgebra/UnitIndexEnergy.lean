import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.WeakStrictUnitSelections

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open FiniteFunctionValues
noncomputable section

def weight {n : ℕ} (f : Fin n → ℕ) : ℤ := ∑i,(f i:ℤ)

lemma twice_staircase (n : ℕ) : 2*(∑i : Fin n,(i.val:ℤ))=(n:ℤ)*((n:ℤ)-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_add,Nat.cast_one]
    nlinarith

lemma staircase_weight (n : ℕ) (f : Weak n) :
    2*weight (staircaseEquiv n f).val=2*weight f.val+(n:ℤ)*((n:ℤ)-1) := by
  change 2*(∑i : Fin n,((f.val i+i.val:ℕ):ℤ))=_
  simp only [Nat.cast_add,Finset.sum_add_distrib,mul_add,twice_staircase,weight]

abbrev UnitIndex (a n : ℕ) := {f : Fin n → ℕ // if a=0 then StrictMono f else Monotone f}

def weakUnitEquiv (a n : ℕ) : Weak n ≃ UnitIndex a n := by
  classical
  by_cases h : a=0
  · exact
      { toFun := fun f=>⟨(staircaseEquiv n f).val,by simpa only [ite_eq_left h] using (staircaseEquiv n f).property⟩
        invFun := fun g=>(staircaseEquiv n).symm ⟨g.val,by simpa only [ite_eq_left h] using g.property⟩
        left_inv := fun f=>(staircaseEquiv n).symm_apply_apply f
        right_inv := fun g=>Subtype.ext (congrArg (fun q : Strict n=>q.val) ((staircaseEquiv n).apply_symm_apply
          ⟨g.val,by simpa only [ite_eq_left h] using g.property⟩)) }
  · exact
      { toFun := fun f=>⟨f.val,by simpa only [ite_eq_right h] using f.property⟩
        invFun := fun g=>⟨g.val,by simpa only [ite_eq_right h] using g.property⟩
        left_inv := fun _=>rfl
        right_inv := fun _=>rfl }

def unitWeight (a n : ℕ) (q : UnitIndex a n) : ℤ := weight q.val

lemma weakUnit_weight (a n : ℕ) (ha : a≤1) (f : Weak n) :
    2*unitWeight a n (weakUnitEquiv a n f)=
      2*weight f.val+(1-(a:ℤ))*(n:ℤ)*((n:ℤ)-1) := by
  by_cases h : a=0
  · subst a
    change 2*weight (staircaseEquiv n f).val=2*weight f.val+(1-(0:ℤ))*(n:ℤ)*((n:ℤ)-1)
    simpa only [sub_zero,one_mul] using staircase_weight n f
  · have he : a=1 := by omega
    subst a
    change 2*weight f.val=2*weight f.val+(1-(1:ℤ))*(n:ℤ)*((n:ℤ)-1)
    simp

lemma weakSym_weight (n : ℕ) (f : Weak n) :
    (((weakSymEquiv n f).val).map (Nat.cast:ℕ→ℤ)).sum=weight f.val := by
  change ((values f.val).map (Nat.cast:ℕ→ℤ)).sum=weight f.val
  simp only [values,Multiset.map_map,weight]
  rfl
end
end ElementaryPositivity.UnitSelections
end
end

end OAI
