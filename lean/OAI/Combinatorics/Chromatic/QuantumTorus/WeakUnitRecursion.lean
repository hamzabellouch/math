import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.UnitIndexEnergy

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
noncomputable section

def prependZero (n : ℕ) (f : Weak n) : Weak (n+1) :=
  ⟨Fin.cons 0 f.val,by
    intro i j
    refine Fin.cases (fun _=>Nat.zero_le _) (fun i=>?_) i
    refine Fin.cases ?_ (fun j hij=>f.property (Fin.succ_le_succ_iff.mp hij)) j
    intro hij
    simp at hij⟩

def deleteZeroEquiv (n : ℕ) : {f : Weak (n+1) // f.val 0=0} ≃ Weak n where
  toFun f:=⟨fun i=>f.val.val i.succ,fun _ _ h=>f.val.property (Fin.succ_le_succ_iff.mpr h)⟩
  invFun f:=⟨prependZero n f,rfl⟩
  left_inv f:=by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun i=>rfl) i
    exact f.property.symm
  right_inv f:=rfl

lemma weak_first_le (n : ℕ) (f : Weak (n+1)) (i : Fin (n+1)) : f.val 0≤f.val i :=
  f.property (Fin.zero_le i)

def shiftOne (n : ℕ) (f : Weak n) : Weak n :=
  ⟨fun i=>f.val i+1,fun _ _ h=>Nat.add_le_add_right (f.property h) 1⟩

def subtractOneEquiv (n : ℕ) : {f : Weak (n+1) // f.val 0≠0} ≃ Weak (n+1) where
  toFun f:=⟨fun i=>f.val.val i-1,fun _ _ h=>Nat.sub_le_sub_right (f.val.property h) 1⟩
  invFun f:=⟨shiftOne (n+1) f,by simp [shiftOne]⟩
  left_inv f:=by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change f.val.val i-1+1=f.val.val i
    have h:=weak_first_le n f.val i
    have h0:=f.property
    omega
  right_inv f:=by
    apply Subtype.ext
    funext i
    change f.val i+1-1=f.val i
    omega

def weakSplit (n : ℕ) : Weak (n+1) ≃ Weak n ⊕ Weak (n+1) :=
  (Equiv.sumCompl (fun f : Weak (n+1)=>f.val 0=0)).symm.trans
    (Equiv.sumCongr (deleteZeroEquiv n) (subtractOneEquiv n))

lemma weight_prependZero (n : ℕ) (f : Weak n) : weight (prependZero n f).val=weight f.val := by
  rw [weight,Fin.sum_univ_succ]
  simp only [prependZero,Fin.cons_zero,Fin.cons_succ,Nat.cast_zero,zero_add]
  rfl

lemma weight_shiftOne (n : ℕ) (f : Weak n) : weight (shiftOne n f).val=weight f.val+n := by
  simp [weight,shiftOne,Finset.sum_add_distrib]

lemma weakSplit_inv_energy (n : ℕ) (k : ℤ) (p : Weak n ⊕ Weak (n+1)) :
    ((n+1:ℕ):ℤ)*k-2*weight (weakSplit n |>.symm p).val=
      Sum.elim (fun f : Weak n=>(n:ℤ)*k-2*weight f.val+k)
        (fun f : Weak (n+1)=>((n+1:ℕ):ℤ)*k-2*weight f.val-2*(n+1)) p := by
  cases p with
  | inl f =>
    change ((n+1:ℕ):ℤ)*k-2*weight (prependZero n f).val=_
    rw [weight_prependZero]
    simp only [Sum.elim_inl,Nat.cast_add,Nat.cast_one]
    ring
  | inr f =>
    change ((n+1:ℕ):ℤ)*k-2*weight (shiftOne (n+1) f).val=_
    rw [weight_shiftOne]
    simp only [Sum.elim_inr,Nat.cast_add,Nat.cast_one]
    ring
end
end ElementaryPositivity.UnitSelections
end
end

end OAI
