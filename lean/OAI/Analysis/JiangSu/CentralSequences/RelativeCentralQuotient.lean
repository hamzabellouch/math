import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.FourEdgeGroupSurgery

namespace OAI

section

noncomputable section
namespace RelativeCentral
open Pureness
open scoped CStarAlgebra

variable {A E : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra E]
variable (j : A →⋆ₙₐ[ℂ] E)

def centralizer : StarSubalgebra ℂ E where
  carrier := {x | ∀ a : A,x*j a=j a*x}
  zero_mem' := by intro a; simp
  one_mem' := by intro a; simp
  add_mem' hx hy := by intro a; simp only [add_mul,mul_add,hx a,hy a]
  mul_mem' hx hy := by intro a; rw [mul_assoc,hy a,←mul_assoc,hx a,mul_assoc]
  algebraMap_mem' c := by intro a; exact Algebra.commutes c (j a)
  star_mem' hx := by
    intro a
    have h := congrArg star (hx (star a))
    simpa only [star_mul,←map_star,star_star] using h.symm

instance centralizer_closed : IsClosed (centralizer j : Set E) := by
  change IsClosed {x : E | ∀ a : A,x*j a=j a*x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun a => isClosed_eq (by fun_prop) (by fun_prop))
instance : CStarAlgebra (centralizer j) := StarSubalgebra.cstarAlgebra _
instance : PartialOrder (centralizer j) := CStarAlgebra.spectralOrder _
instance : StarOrderedRing (centralizer j) := CStarAlgebra.spectralOrderedRing _

def annihilatorIdeal : TwoSidedIdeal (centralizer j) :=
  TwoSidedIdeal.mk' {x | ∀ a : A,(x:E)*j a=0 ∧ j a*(x:E)=0}
    (by intro a; simp)
    (by
      intro x y hx hy a
      change ((x:E)+(y:E))*j a=0 ∧ j a*((x:E)+(y:E))=0
      simp only [add_mul,mul_add,hx a,hy a,zero_add,and_self])
    (by
      intro x hx a
      change (-(x:E))*j a=0 ∧ j a*(-(x:E))=0
      simp only [neg_mul,mul_neg,hx a,neg_zero,and_self])
    (by
      intro x y hy a
      change ((x:E)*(y:E))*j a=0 ∧ j a*((x:E)*(y:E))=0
      constructor
      · rw [mul_assoc,(hy a).1,mul_zero]
      · rw [←mul_assoc,←x.property a,mul_assoc,(hy a).2,mul_zero])
    (by
      intro x y hx a
      change ((x:E)*(y:E))*j a=0 ∧ j a*((x:E)*(y:E))=0
      constructor
      · rw [mul_assoc,y.property a,←mul_assoc,(hx a).1,zero_mul]
      · rw [←mul_assoc,(hx a).2,zero_mul])

@[simp] lemma mem_annihilator (x : centralizer j) :
    x∈annihilatorIdeal j ↔ ∀ a : A,(x:E)*j a=0 ∧ j a*(x:E)=0 := by
  simp only [annihilatorIdeal,TwoSidedIdeal.mem_mk',Set.mem_ofPred_eq]

def annihilator : ClosedStarIdeal (centralizer j) where
  ideal := annihilatorIdeal j
  star_mem := by
    intro x hx
    rw [mem_annihilator] at hx ⊢
    intro a
    change star (x:E)*j a=0 ∧ j a*star (x:E)=0
    constructor
    · have h := congrArg star ((hx (star a)).2)
      simpa only [star_mul,←map_star,star_star,star_zero] using h
    · have h := congrArg star ((hx (star a)).1)
      simpa only [star_mul,←map_star,star_star,star_zero] using h
  isClosed := by
    have hs : (annihilatorIdeal j : Set (centralizer j))=
        {x : centralizer j | ∀ a : A,(x:E)*j a=0 ∧ j a*(x:E)=0} := by ext x; exact mem_annihilator j x
    rw [hs]
    simp only [Set.ofPred_forall,Set.ofPred_and]
    exact isClosed_iInter (fun a => (isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_eq (by fun_prop) continuous_const))

abbrev Quotient := (annihilator j).Quotient
def quotientMap : centralizer j →⋆ₐ[ℂ] Quotient j := (annihilator j).quotientStarHom

lemma quotient_eq_iff (x y : centralizer j) : quotientMap j x=quotientMap j y ↔
    ∀ a : A,((x:E)-(y:E))*j a=0 ∧ j a*((x:E)-(y:E))=0 := by
  change (annihilatorIdeal j).ringCon.mk' x=(annihilatorIdeal j).ringCon.mk' y ↔ _
  have h : (annihilatorIdeal j).ringCon.mk' x=(annihilatorIdeal j).ringCon.mk' y ↔
      (annihilatorIdeal j).ringCon x y := Quotient.eq
  rw [h,TwoSidedIdeal.rel_iff,mem_annihilator]
  rfl

lemma norm_mul_le_quotient (x : centralizer j) (a : A) :
    ‖(x:E)*j a‖≤‖quotientMap j x‖*‖j a‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/(‖j a‖+1)
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨y,hy,hyn⟩ := (annihilator j).quotient_norm_lt_rep (quotientMap j x) hδ
  have heq : (y:E)*j a=(x:E)*j a := by
    have hz := ((quotient_eq_iff j y x).mp hy a).1
    rwa [sub_mul,sub_eq_zero] at hz
  calc
    _=‖(y:E)*j a‖ := congrArg norm heq.symm
    _≤‖(y:E)‖*‖j a‖ := norm_mul_le _ _
    _≤(‖quotientMap j x‖+δ)*‖j a‖ := mul_le_mul_of_nonneg_right hyn.le (norm_nonneg _)
    _≤‖quotientMap j x‖*‖j a‖+ε := by
      have hd : δ*(‖j a‖+1)=ε :=
        div_mul_cancel₀ ε (ne_of_gt (by positivity : 0 < ‖j a‖+1))
      rw [add_mul]
      exact add_le_add le_rfl
        ((mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hδ.le).trans_eq hd)

lemma norm_mul_sub_le_quotient (x y : centralizer j) (a : A) :
    ‖((x:E)-(y:E))*j a‖≤‖quotientMap j x-quotientMap j y‖*‖j a‖ := by
  have h := norm_mul_le_quotient j (x-y) a
  rw [map_sub] at h
  exact h

lemma quotient_nontrivial (hj : ∃ a : A,j a≠0) : Nontrivial (Quotient j) := by
  obtain ⟨a,ha⟩ := hj
  refine ⟨⟨1,0,?_⟩⟩
  intro h
  have he : quotientMap j 1=quotientMap j 0 := by simpa only [map_one,map_zero] using h
  have hz := ((quotient_eq_iff j 1 0).mp he a).1
  apply ha
  simpa only [OneMemClass.coe_one,ZeroMemClass.coe_zero,sub_zero,one_mul] using hz

lemma norm_right_mul_sub_le_quotient (x y : centralizer j) (a : A) :
    ‖j a*((x:E)-(y:E))‖≤‖quotientMap j x-quotientMap j y‖*‖j a‖ := by
  rw [mul_sub,←x.property a,←y.property a,←sub_mul]
  exact norm_mul_sub_le_quotient j x y a

end RelativeCentral

end
end

end OAI
