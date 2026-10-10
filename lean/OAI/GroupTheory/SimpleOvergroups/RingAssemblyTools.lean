import Mathlib
import OAI.GroupTheory.BooneHigman.Basic
import OAI.GroupTheory.BooneHigman.Contracted
import OAI.GroupTheory.BooneHigman.Corners
import OAI.GroupTheory.BooneHigman.MonoidAlgebras
import OAI.GroupTheory.BooneHigman.PartialAffine
import OAI.GroupTheory.FiniteType.Steinberg

namespace OAI

noncomputable section
namespace SimpleFInftyOvergroups.RingAssembly
open scoped Classical TensorProduct
open FiniteAlgebraicEnvelopes

section Quotient
variable {R : Type*} [Ring R] (r : R → R → Prop)

def differences : Set R := (fun p : R × R => p.1-p.2) '' {p | r p.1 p.2}

 theorem differences_finite (h : {p : R × R | r p.1 p.2}.Finite) :
    (differences r).Finite := h.image _

 theorem ker_ringQuot : TwoSidedIdeal.ker (RingQuot.mkRingHom r) =
    TwoSidedIdeal.span (differences r) := by
  let I := TwoSidedIdeal.span (differences r)
  have respects : ∀ ⦃a b : R⦄, r a b → I.ringCon.mk' a=I.ringCon.mk' b := by
    intro a b hab
    apply I.ringCon.eq.mpr
    apply (I.rel_iff a b).mpr
    exact TwoSidedIdeal.subset_span ⟨(a,b),hab,rfl⟩
  let t : RingQuot r →+* I.ringCon.Quotient := RingQuot.lift ⟨I.ringCon.mk',respects⟩
  apply le_antisymm
  · intro x hx
    have hx' := congrArg t ((TwoSidedIdeal.mem_ker _).mp hx)
    have hq : I.ringCon.mk' x=0 := by
      simpa only [t,RingQuot.lift_mkRingHom_apply,map_zero] using hx'
    have hi := (TwoSidedIdeal.mem_ker I.ringCon.mk').mpr hq
    simpa only [TwoSidedIdeal.ker_ringCon_mk'] using hi
  · apply TwoSidedIdeal.span_le.mpr
    rintro x ⟨⟨a,b⟩,hab,rfl⟩
    apply (TwoSidedIdeal.mem_ker _).mpr
    rw [map_sub,RingQuot.mkRingHom_rel hab,sub_self]
end Quotient

section Corner
variable {R S : Type*} [Ring R] [Ring S]

theorem supportIdempotent (f : R →ₙ+* S) : IsIdempotentElem (f 1) := by
  change f 1*f 1=f 1
  rw [←map_mul,one_mul]

def toCorner (f : R →ₙ+* S) : R →+* (supportIdempotent f).Corner where
  toFun x := ⟨f x,(Subsemigroup.mem_corner_iff (supportIdempotent f)).mpr
    ⟨by rw [←map_mul,one_mul],by rw [←map_mul,mul_one]⟩⟩
  map_one' := rfl
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f x y)
  map_mul' x y := Subtype.ext (map_mul f x y)

 theorem toCorner_injective (f : R →ₙ+* S) (hf : Function.Injective f) :
    Function.Injective (toCorner f) := by
  intro x y hxy
  exact hf (congrArg Subtype.val hxy)
end Corner

section Contracted
variable {k M : Type*} [CommRing k] [Nontrivial k] [MonoidWithZero M]

 theorem monoidBasis_injective : Function.Injective (ContractedPresentation.monoidBasis k (M:=M)) := by
  intro x y hxy
  change Contracted.basis k M x 1=Contracted.basis k M y 1 at hxy
  by_contra hne
  by_cases hx : x=0
  · have hy : y≠0 := by intro hy; exact hne (hx.trans hy.symm)
    have hh := congrArg (Contracted.coefficient (k:=k) y hy) hxy
    simp [Contracted.coefficient_basis,Ne.symm hne] at hh
  · have hh := congrArg (Contracted.coefficient (k:=k) x hx) hxy
    simp [Contracted.coefficient_basis,hne] at hh

def monoidBasis₀ : M →*₀ Contracted.Algebra k M :=
  { ContractedPresentation.monoidBasis k with map_zero' := Contracted.basis_zero k M 1 }
end Contracted

variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]
open PartialAffine.Corner

def binaryS : Fin 2 → MonoidAlgebra k PartialAffine.monoid := ![s0 k,s1 k]
def binaryD : Fin 2 → MonoidAlgebra k PartialAffine.monoid := ![t0 k,t1 k]

lemma q_binaryS (i : Fin 2) : q k*binaryS i=binaryS i := by
  fin_cases i
  · exact q_s0 k
  · exact q_s1 k
lemma binaryS_q (i : Fin 2) : binaryS i*q k=binaryS i := by
  fin_cases i
  · exact s0_q k
  · exact s1_q k
lemma q_binaryD (i : Fin 2) : q k*binaryD i=binaryD i := by
  fin_cases i
  · exact q_t0 k
  · exact q_t1 k
lemma binaryD_q (i : Fin 2) : binaryD i*q k=binaryD i := by
  fin_cases i
  · exact t0_q k
  · exact t1_q k
lemma binaryDS (i j : Fin 2) : binaryD i*binaryS j=if i=j then q k else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [binaryS,binaryD,t0_s0,t0_s1,t1_s0,t1_s1]
lemma binary_partition : binaryS (k:=k) 0*binaryD 0+binaryS 1*binaryD 1=q k :=
  s0_t0_add_s1_t1 k

variable (ξ : B ⊗[k] MonoidAlgebra k PartialAffine.monoid →ₙₐ[k] B)

def binaryPhi : B →ₙₐ[k] B := ξ.comp (cornerTensor k B)

lemma binaryPhi_apply (a : B) : binaryPhi ξ a=ξ (a⊗ₜ[k] q k) := rfl

lemma binary_constant_commute (c : MonoidAlgebra k PartialAffine.monoid)
    (hqc : q k*c=c) (hcq : c*q k=c) (a : B) :
    Commute (ξ (1⊗ₜ[k] c)) (binaryPhi ξ a) := by
  change ξ (1⊗ₜ[k] c)*binaryPhi ξ a=binaryPhi ξ a*ξ (1⊗ₜ[k] c)
  rw [binaryPhi_apply,←map_mul,←map_mul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,hqc,hcq]

def binaryData : CompressedSplittings.BinaryData (binaryPhi ξ : B →ₙ+* B) where
  s i := ξ (1⊗ₜ[k] binaryS i)
  d i := ξ (1⊗ₜ[k] binaryD i)
  s_left i := by
    change ξ (1⊗ₜ[k] q k)*ξ (1⊗ₜ[k] binaryS i)=_
    rw [←map_mul,Algebra.TensorProduct.tmul_mul_tmul,one_mul,q_binaryS]
  s_right i := by
    change ξ (1⊗ₜ[k] binaryS i)*ξ (1⊗ₜ[k] q k)=_
    rw [←map_mul,Algebra.TensorProduct.tmul_mul_tmul,one_mul,binaryS_q]
  d_left i := by
    change ξ (1⊗ₜ[k] q k)*ξ (1⊗ₜ[k] binaryD i)=_
    rw [←map_mul,Algebra.TensorProduct.tmul_mul_tmul,one_mul,q_binaryD]
  d_right i := by
    change ξ (1⊗ₜ[k] binaryD i)*ξ (1⊗ₜ[k] q k)=_
    rw [←map_mul,Algebra.TensorProduct.tmul_mul_tmul,one_mul,binaryD_q]
  s_commute i := binary_constant_commute ξ (binaryS i) (q_binaryS i) (binaryS_q i)
  d_commute i := binary_constant_commute ξ (binaryD i) (q_binaryD i) (binaryD_q i)
  ds i j := by
    rw [←map_mul,Algebra.TensorProduct.tmul_mul_tmul,one_mul,binaryDS]
    split_ifs
    · rfl
    · rw [TensorProduct.tmul_zero,map_zero]
  partition := by
    rw [←map_mul,←map_mul,←map_add]
    simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,←TensorProduct.tmul_add,binary_partition]
    rfl

 theorem binaryPhi_injective (hξ : Function.Injective ξ) : Function.Injective (binaryPhi ξ) :=
  hξ.comp (cornerTensor_injective k B)

end SimpleFInftyOvergroups.RingAssembly
end

end OAI
