import Mathlib
import OAI.GroupTheory.FiniteType.ClassifyingSpacesFiniteExtensionGeometricFromProducts

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace PrefixPermutation
variable {R Y : Type*} [Ring R] [DecidableEq Y]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)

include hTS in
lemma prefix_injective (he : e≠0) : Function.Injective S := by
  intro y z h
  by_contra hyz
  have eq := congrArg (fun r => T y*r) h
  apply he
  simpa [hTS,hyz] using eq

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (x : ι → Y) (hx : Function.Injective x)

def matrixPart (σ : Equiv.Perm ι) : R := ∑ i, S (x (σ i))*T (x i)

def support : R := ∑ i, S (x i)*T (x i)

omit [DecidableEq Y] [DecidableEq ι] in
@[simp] lemma partial_one : matrixPart S T x 1=support S T x := rfl

include hTS hSe hx in
lemma partial_mul (σ τ : Equiv.Perm ι) :
    matrixPart S T x σ*matrixPart S T x τ=matrixPart S T x (σ*τ) := by
  classical
  unfold matrixPart
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have heq (i : ι) : S (x (σ i))*T (x i)*(S (x (τ j))*T (x j))=
      if i=τ j then S (x (σ (τ j)))*T (x j) else 0 := by
    rw [mul_assoc,← mul_assoc (T (x i)),hTS]
    by_cases h : i=τ j
    · subst i; simp [← mul_assoc,hSe]
    · rw [ite_eq_right (fun he => h (hx he)),zero_mul,mul_zero,ite_eq_right h]
  simp_rw [heq]
  simp

include hTS hSe hx in
lemma support_mul (σ : Equiv.Perm ι) : support S T x*matrixPart S T x σ=matrixPart S T x σ := by
  simpa only [partial_one,one_mul] using partial_mul e S T hTS hSe x hx 1 σ

include hTS hSe hx in
lemma mul_support (σ : Equiv.Perm ι) : matrixPart S T x σ*support S T x=matrixPart S T x σ := by
  simpa only [partial_one,mul_one] using partial_mul e S T hTS hSe x hx σ 1

include hTS hSe hx in
lemma support_idempotent : support S T x*support S T x=support S T x := by
  simpa only [partial_one] using support_mul e S T hTS hSe x hx 1

def value (σ : Equiv.Perm ι) : R := 1-support S T x+matrixPart S T x σ

omit [DecidableEq Y] [DecidableEq ι] in
@[simp] lemma value_one : value S T x 1=1 := by simp [value]

include hTS hSe hx in
lemma value_mul (σ τ : Equiv.Perm ι) : value S T x (σ*τ)=value S T x σ*value S T x τ := by
  have hpp := support_idempotent e S T hTS hSe x hx
  have hpτ := support_mul e S T hTS hSe x hx τ
  have hσp := mul_support e S T hTS hSe x hx σ
  have hστ := partial_mul e S T hTS hSe x hx σ τ
  unfold value
  noncomm_ring [hpp,hpτ,hσp,hστ]

def units : Equiv.Perm ι →* Rˣ where
  toFun σ := {
    val := value S T x σ
    inv := value S T x σ⁻¹
    val_inv := by rw [← value_mul e S T hTS hSe x hx,mul_inv_cancel,value_one]
    inv_val := by rw [← value_mul e S T hTS hSe x hx,inv_mul_cancel,value_one] }
  map_one' := Units.ext (value_one S T x)
  map_mul' σ τ := Units.ext (value_mul e S T hTS hSe x hx σ τ)

include hTS hSe hx in
lemma partial_prefix (σ : Equiv.Perm ι) (j : ι) :
    matrixPart S T x σ*S (x j)=S (x (σ j)) := by
  classical
  unfold matrixPart
  rw [Finset.sum_mul]
  have heq (i : ι) : S (x (σ i))*T (x i)*S (x j)=if i=j then S (x (σ j)) else 0 := by
    rw [mul_assoc,hTS]
    by_cases h : i=j
    · subst i; simpa using hSe (x (σ j))
    · rw [ite_eq_right (fun he => h (hx he)),mul_zero,ite_eq_right h]
  simp_rw [heq]
  simp

include hTS hSe hx in
lemma value_prefix (σ : Equiv.Perm ι) (j : ι) :
    value S T x σ*S (x j)=S (x (σ j)) := by
  have h := partial_prefix e S T hTS hSe x hx 1 j
  simp only [Equiv.Perm.one_apply] at h
  simpa [value,add_mul,sub_mul,partial_prefix e S T hTS hSe x hx σ j] using
    (show S (x j)-support S T x*S (x j)+S (x (σ j))=S (x (σ j)) by rw [← partial_one,h]; abel)

omit [DecidableEq ι] in
include hTS in
lemma partial_outside (σ : Equiv.Perm ι) (z : Y) (hz : z∉Set.range x) :
    matrixPart S T x σ*S z=0 := by
  unfold matrixPart
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  rw [mul_assoc,hTS,ite_eq_right (fun h => hz ⟨i,h⟩),mul_zero]

omit [DecidableEq ι] in
include hTS in
lemma value_outside (σ : Equiv.Perm ι) (z : Y) (hz : z∉Set.range x) :
    value S T x σ*S z=S z := by
  have h := partial_outside e S T hTS x 1 z hz
  simp only [partial_one] at h
  simp only [value,add_mul,sub_mul,one_mul,h,partial_outside e S T hTS x σ z hz,sub_zero,add_zero]

end PrefixPermutation

namespace NoncommElementary
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]
                                                                          
def columnPerm (u : (Matrix n n R)ˣ) : Equiv.Perm (n → R) where
  toFun := Matrix.mulVec u.val
  invFun := Matrix.mulVec u.inv
  left_inv x := by rw [Matrix.mulVec_mulVec, u.inv_val, Matrix.one_mulVec]
  right_inv x := by rw [Matrix.mulVec_mulVec, u.val_inv, Matrix.one_mulVec]

def columnAction : (Matrix n n R)ˣ →* Equiv.Perm (n → R) where
  toFun := columnPerm
  map_one' := by ext x i; simp [columnPerm]
  map_mul' u v := by
    ext x i
    change (u.val * v.val).mulVec x i = u.val.mulVec (v.val.mulVec x) i
    rw [Matrix.mulVec_mulVec]

lemma columnAction_injective : Function.Injective (columnAction (R:=R) (n:=n)) := by
  intro u v h
  apply Units.ext
  ext i j
  have hh := congrArg (fun a : Equiv.Perm (n → R) => a (Pi.single j 1) i) h
  simpa [columnAction,columnPerm,Matrix.mulVec, dotProduct, Pi.single_apply] using hh

lemma root_mulVec (i j : n) (h : i≠j) (a : R) (x : n → R) :
    Matrix.mulVec (root i j h a).val x = x+Pi.single i (a*x j) := by
  ext k
  simp [root_val,Matrix.add_mulVec,Matrix.single_mulVec,Pi.single]

lemma position_mulVec (i : n) (v : Rˣ) (a : R) :
    Matrix.mulVec (position i v).val (Pi.single i a)=Pi.single i (v.val*a) := by
  ext k
  by_cases hk : k=i
  · subst k; simp [position_val,Matrix.single]
  · simp [position_val,Matrix.single,hk,Ne.symm hk]

def exchange (i j : n) (h : i≠j) (d : R) : (Matrix n n R)ˣ :=
  root i j h d * root j i h.symm (-d) * root i j h d

lemma exchange_mem (i j : n) (h : i≠j) (d : R) : exchange i j h d∈elementary :=
  (elementary (R:=R)).mul_mem
    ((elementary (R:=R)).mul_mem (root_mem _ _ _ _) (root_mem _ _ _ _))
    (root_mem _ _ _ _)

lemma exchange_val (i j : n) (h : i≠j) (d : R) (hd : d*d=d) :
    (exchange i j h d).val=1-Matrix.single i i d-Matrix.single j j d+
      Matrix.single i j d-Matrix.single j i d := by
  simp only [exchange,Units.val_mul,root_val]
  simp [mul_add,add_mul, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ h.symm,hd,
    ← Matrix.single_neg]
  abel

lemma exchange_fixes (i j : n) (h : i≠j) (d a : R) (ha : d*a=0) :
    Matrix.mulVec (exchange i j h d).val (Pi.single i a)=Pi.single i a := by
  simp only [exchange,Units.val_mul,← Matrix.mulVec_mulVec,root_mulVec]
  simp [Ne.symm h,ha]

lemma exchange_move (i j : n) (h : i≠j) (d : R) (hd : d*d=d) (v : Rˣ)
    (hl : d*(v.val-1)=v.val-1) (hr : (v.val-1)*d=v.val-1) :
    exchange i j h d * position i v * (exchange i j h d)⁻¹=position j v := by
  apply (mul_right_cancel_iff).mp
  rw [mul_assoc,inv_mul_cancel,mul_one]
  apply Units.ext
  simp only [Units.val_mul,exchange_val i j h d hd,position_val]
  simp [mul_add,add_mul,sub_mul,mul_sub,
    Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ h.symm,hl,hr]
  abel

end NoncommElementary

namespace PrefixPermutation
variable {R Y ι : Type*} [Ring R] [DecidableEq Y] [Fintype ι] [DecidableEq ι]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)
variable (x : ι → Y) (hx : Function.Injective x)

def complement (ψ : R →ₙ+* R) : R := 1-ψ (support S T x)

include hTS hSe hx in
lemma complement_idempotent (ψ : R →ₙ+* R) :
    complement S T x ψ * complement S T x ψ = complement S T x ψ := by
  have hp : ψ (support S T x)*ψ (support S T x)=ψ (support S T x) := by
    rw [← map_mul,support_idempotent e S T hTS hSe x hx]
  unfold complement
  noncomm_ring [hp]

include hTS hSe hx in
lemma complement_prefix (ψ : R →ₙ+* R) (j : ι) :
    complement S T x ψ * ψ (S (x j))=0 := by
  have h := partial_prefix e S T hTS hSe x hx 1 j
  change support S T x*S (x j)=S (x j) at h
  rw [complement,sub_mul,one_mul,← map_mul,h,sub_self]

omit [DecidableEq Y] [DecidableEq ι] in
lemma complement_support (ψ : R →ₙ+* R) (a : R)
    (hS : ∀ j, a*S (x j)=0) (hT : ∀ j, T (x j)*a=0) :
    complement S T x ψ*ψ a=ψ a ∧ ψ a*complement S T x ψ=ψ a := by
  have hl : support S T x*a=0 := by
    simp [support,Finset.sum_mul,mul_assoc,hT]
  have hr : a*support S T x=0 := by
    simp [support,Finset.mul_sum,← mul_assoc,hS]
  constructor
  · rw [complement,sub_mul,one_mul,← map_mul,hl,map_zero,sub_zero]
  · rw [complement,mul_sub,mul_one,← map_mul,hr,map_zero,sub_zero]

end PrefixPermutation

end

end OAI
