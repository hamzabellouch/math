import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormTraceKernelSigma
import OAI.Analysis.JiangSu.Traces.NormAnnihilatorTraceKernel
import OAI.Analysis.JiangSu.Nonunital.ClosedIdealBasic

namespace OAI

section

noncomputable section
namespace NonunitalGamma
open Pureness CurrentMain Filter Topology NormUltra
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

def normCentralizer : NonUnitalStarSubalgebra ℂ N where
  carrier := {x | ∀ a : A, x*normInclusion U a=normInclusion U a*x}
  zero_mem' := by intro a; simp only [zero_mul,mul_zero]
  add_mem' hx hy := by intro a; simp only [add_mul,mul_add,hx a,hy a]
  mul_mem' hx hy := by
    intro a
    rw [mul_assoc,hy a,←mul_assoc,hx a,mul_assoc]
  smul_mem' c x hx := by intro a; simp only [smul_mul_assoc,mul_smul_comm,hx a]
  star_mem' hx := by
    intro a
    have h := congrArg star (hx (star a))
    simpa only [star_mul,←map_star,star_star] using h.symm

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma mem_normCentralizer (x : N) : x ∈ normCentralizer (A := A) U ↔
    ∀ a : A, x*normInclusion U a=normInclusion U a*x := Iff.rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma normCentralizer_closed : IsClosed (normCentralizer (A := A) U : Set N) := by
  change IsClosed {x : N | ∀ a : A, x*normInclusion U a=normInclusion U a*x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun a => isClosed_eq (by fun_prop) (by fun_prop))

instance : CompleteSpace (normCentralizer (A := A) U) := (normCentralizer_closed U).completeSpace_coe
instance : NonUnitalCStarAlgebra (normCentralizer (A := A) U) where
  norm_mul_self_le x := CStarRing.norm_mul_self_le x.1
instance (priority := 1100) : LE (normCentralizer (A := A) U) := (CStarAlgebra.spectralOrder _).toLE
instance (priority := 1100) : Preorder (normCentralizer (A := A) U) := (CStarAlgebra.spectralOrder _).toPreorder
instance (priority := 1100) : PartialOrder (normCentralizer (A := A) U) := CStarAlgebra.spectralOrder _
instance : StarOrderedRing (normCentralizer (A := A) U) := CStarAlgebra.spectralOrderedRing _

def normCentralInclusion : normCentralizer (A := A) U →⋆ₙₐ[ℂ] N where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

def normAnnihilator : NonunitalClosedIdeal.Ideal (normCentralizer (A := A) U) where
  module := {
    carrier := {x | ∀ a : A, (x:N)*normInclusion U a=0 ∧ normInclusion U a*(x:N)=0}
    zero_mem' := by
      intro a
      change (0:N)*normInclusion U a=0 ∧ normInclusion U a*(0:N)=0
      simp only [zero_mul,mul_zero,and_self]
    add_mem' hx hy := by
      intro a
      simp only [NonUnitalStarSubalgebra.coe_add,add_mul,mul_add,hx a,hy a,zero_add,and_self]
    smul_mem' c x hx := by
      intro a
      simp only [NonUnitalStarSubalgebra.coe_smul,smul_mul_assoc,mul_smul_comm,hx a,smul_zero,and_self] }
  mul_left x y hy := by
    intro a
    change ((x:N)*(y:N))*normInclusion U a=0 ∧ normInclusion U a*((x:N)*(y:N))=0
    constructor
    · rw [mul_assoc,(hy a).1,mul_zero]
    · rw [←mul_assoc,←x.property a,mul_assoc,(hy a).2,mul_zero]
  mul_right x y hx := by
    intro a
    change ((x:N)*(y:N))*normInclusion U a=0 ∧ normInclusion U a*((x:N)*(y:N))=0
    constructor
    · rw [mul_assoc,y.property a,←mul_assoc,(hx a).1,zero_mul]
    · rw [←mul_assoc,(hx a).2,zero_mul]
  star_mem x hx := by
    intro a
    change star (x:N)*normInclusion U a=0 ∧ normInclusion U a*star (x:N)=0
    constructor
    · have h := congrArg star ((hx (star a)).2)
      simpa only [star_mul,←map_star,star_star,star_zero] using h
    · have h := congrArg star ((hx (star a)).1)
      simpa only [star_mul,←map_star,star_star,star_zero] using h
  closed := by
    change IsClosed {x : normCentralizer (A := A) U | ∀ a : A,
      (x:N)*normInclusion U a=0 ∧ normInclusion U a*(x:N)=0}
    simp only [Set.ofPred_forall,Set.ofPred_and]
    refine isClosed_iInter (fun a => ?_)
    exact (isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_eq (by fun_prop) continuous_const)

abbrev CentralSequenceAlgebra := NonunitalClosedIdeal.QuotientAlgebra (normAnnihilator (A := A) U)

def centralSequenceQuotient : normCentralizer (A := A) U →⋆ₙₐ[ℂ] CentralSequenceAlgebra (A := A) U :=
  NonunitalClosedIdeal.QuotientAlgebra.mkHom _

section Unit
variable [TopologicalSpace.SeparableSpace A] [Fact ((U : Filter ℕ) ≤ atTop)]

def centralLocalUnit : normCentralizer (A := A) U :=
  ⟨(exists_norm_central_local_unit (A := A) U Fact.out).choose,fun a =>
    ((exists_norm_central_local_unit (A := A) U Fact.out).choose_spec.2.2 a).1.trans
      ((exists_norm_central_local_unit (A := A) U Fact.out).choose_spec.2.2 a).2.symm⟩

lemma centralLocalUnit_mul (a : A) :
    (centralLocalUnit (A := A) U:N)*normInclusion U a=normInclusion U a :=
  ((exists_norm_central_local_unit (A := A) U Fact.out).choose_spec.2.2 a).1
lemma mul_centralLocalUnit (a : A) :
    normInclusion U a*(centralLocalUnit (A := A) U:N)=normInclusion U a :=
  ((exists_norm_central_local_unit (A := A) U Fact.out).choose_spec.2.2 a).2

instance : One (CentralSequenceAlgebra (A := A) U) := ⟨centralSequenceQuotient U (centralLocalUnit U)⟩

lemma centralSequence_one_mul (x : CentralSequenceAlgebra (A := A) U) : 1*x=x := by
  obtain ⟨x,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) x
  apply (NonunitalClosedIdeal.QuotientAlgebra.mk_eq_mk_iff _ _ _).mpr
  intro a
  change (((centralLocalUnit (A := A) U:N)*(x:N)-(x:N))*normInclusion U a=0) ∧
    (normInclusion U a*((centralLocalUnit (A := A) U:N)*(x:N)-(x:N))=0)
  constructor
  · rw [sub_mul,mul_assoc,x.property a,←mul_assoc,centralLocalUnit_mul,sub_self]
  · rw [mul_sub,←mul_assoc,mul_centralLocalUnit,sub_self]

lemma centralSequence_mul_one (x : CentralSequenceAlgebra (A := A) U) : x*1=x := by
  obtain ⟨x,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) x
  apply (NonunitalClosedIdeal.QuotientAlgebra.mk_eq_mk_iff _ _ _).mpr
  intro a
  change (((x:N)*(centralLocalUnit (A := A) U:N)-(x:N))*normInclusion U a=0) ∧
    (normInclusion U a*((x:N)*(centralLocalUnit (A := A) U:N)-(x:N))=0)
  constructor
  · rw [sub_mul,mul_assoc,centralLocalUnit_mul,sub_self]
  · rw [mul_sub,←mul_assoc,←x.property a,mul_assoc,mul_centralLocalUnit,sub_self]

instance : Monoid (CentralSequenceAlgebra (A := A) U) where
  one_mul := centralSequence_one_mul U
  mul_one := centralSequence_mul_one U

instance : Ring (CentralSequenceAlgebra (A := A) U) where
  natCast n := n • (1 : CentralSequenceAlgebra (A := A) U)
  natCast_zero := zero_smul _ _
  natCast_succ n := by simp only [add_smul,one_smul]
  intCast z := z • (1 : CentralSequenceAlgebra (A := A) U)
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc := negSucc_zsmul _

instance : Algebra ℂ (CentralSequenceAlgebra (A := A) U) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm
instance : NormedRing (CentralSequenceAlgebra (A := A) U) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := norm_mul_le
instance : NormedAlgebra ℂ (CentralSequenceAlgebra (A := A) U) where
  norm_smul_le := norm_smul_le
instance : CStarAlgebra (CentralSequenceAlgebra (A := A) U) where
  norm_mul_self_le := CStarRing.norm_mul_self_le
instance : PartialOrder (CentralSequenceAlgebra (A := A) U) := CStarAlgebra.spectralOrder _
instance : StarOrderedRing (CentralSequenceAlgebra (A := A) U) := CStarAlgebra.spectralOrderedRing _

end Unit
end NonunitalGamma

end
end

section

noncomputable section
namespace NonunitalGamma
open Pureness CurrentMain Filter Topology NormUltra
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)]
variable [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
local notation "T" => (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "F" => CentralSequenceAlgebra (A := A) U
local notation "q" => NonunitalClosedIdeal.QuotientAlgebra.mk (normAnnihilator (A := A) U)

def centralSequenceToTracialNonunital : F →⋆ₙₐ[ℂ] FamilyUltrapower T U where
  toFun := Quotient.lift (fun x : normCentralizer (A := A) U => normToTracial U (x:N)) (by
    intro x y h
    change (normAnnihilator U).module.quotientRel x y at h
    rw [Submodule.quotientRel_def] at h
    have he := norm_annihilator_in_trace_kernel U ((x:N)-(y:N)) (fun a => (h a).1)
    rw [map_sub,sub_eq_zero] at he
    exact he)
  map_zero' := map_zero (normToTracial U)
  map_add' x y := by
    obtain ⟨x,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) x
    obtain ⟨y,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) y
    exact map_add (normToTracial U) (x:N) (y:N)
  map_mul' x y := by
    obtain ⟨x,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) x
    obtain ⟨y,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) y
    exact map_mul (normToTracial U) (x:N) (y:N)
  map_smul' c x := by
    obtain ⟨x,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) x
    exact map_smul (normToTracial U) c (x:N)
  map_star' x := by
    obtain ⟨x,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) x
    exact map_star (normToTracial U) (x:N)

@[simp] lemma centralSequenceToTracialNonunital_mk (x : normCentralizer (A := A) U) :
    centralSequenceToTracialNonunital U (q x)=normToTracial U (x:N) := rfl

lemma centralSequenceToTracialNonunital_one : centralSequenceToTracialNonunital (A := A) U 1=1 := by
  apply sub_eq_zero.mp
  apply tracial_annihilator_zero U
  intro a
  change (normToTracial U (centralLocalUnit (A := A) U:N)-1)*quotientInclusion U a=0
  rw [sub_mul,one_mul,←normToTracial_inclusion,←map_mul,centralLocalUnit_mul,sub_self]

def centralSequenceToTracial : F →⋆ₐ[ℂ] FamilyUltrapower T U where
  toFun := centralSequenceToTracialNonunital U
  map_zero' := map_zero (centralSequenceToTracialNonunital U)
  map_add' := map_add (centralSequenceToTracialNonunital U)
  map_mul' := map_mul (centralSequenceToTracialNonunital U)
  map_one' := centralSequenceToTracialNonunital_one U
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,centralSequenceToTracialNonunital_one,
      Algebra.algebraMap_eq_smul_one]
  map_star' := map_star (centralSequenceToTracialNonunital U)

@[simp] lemma centralSequenceToTracial_mk (x : normCentralizer (A := A) U) :
    centralSequenceToTracial U (q x)=normToTracial U (x:N) := rfl

lemma centralSequenceToTracial_commutes (x : F) (a : A) :
    centralSequenceToTracial U x*quotientInclusion U a=
      quotientInclusion U a*centralSequenceToTracial U x := by
  obtain ⟨x,rfl⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) x
  rw [centralSequenceToTracial_mk]
  simpa only [map_mul,normToTracial_inclusion] using congrArg (normToTracial U) (x.property a)

theorem centralSequenceToTracial_range (y : FamilyUltrapower T U) :
    y ∈ Set.range (centralSequenceToTracial (A := A) U) ↔
      ∀ a : A, y*quotientInclusion U a=quotientInclusion U a*y := by
  constructor
  · rintro ⟨x,rfl⟩
    exact centralSequenceToTracial_commutes U x
  · intro hy
    obtain ⟨x,hx,hc⟩ := normToTracial_central_surjective U Fact.out y hy
    exact ⟨q ⟨x,hc⟩,hx⟩

end NonunitalGamma

end
end

end OAI
