import Mathlib
import OAI.Algebra.GroupRing.CellModule
import OAI.Algebra.GroupRing.ContiguousSplit

namespace OAI



section
namespace TorsionFreeZeroDivisors.RelationArea
open scoped Classical BigOperators
open AlgebraicPictures CellModule
noncomputable section
variable {A I : Type} (rel : I→List (A×Bool))
abbrev G := PresentedGroup (relations rel)
abbrev N := Subgroup.normalClosure (relations rel)
abbrev q : FreeGroup A→*G rel := PresentedGroup.mk (relations rel)
def term (t : Term (A:=A) (I:=I)) : CellModule.Module (G rel) I :=
  if t.positive then Finsupp.single (q rel (FreeGroup.mk t.connector),t.index) 1
  else -Finsupp.single (q rel (FreeGroup.mk t.connector),t.index) 1
def total (ts : List (Term (A:=A) (I:=I))) : CellModule.Module (G rel) I := (ts.map (term rel)).sum
lemma total_append (s t : List (Term (A:=A) (I:=I))) : total rel (s++t)=total rel s+total rel t := by
  simp only [total,List.map_append,List.sum_append]
lemma total_reverse_flip (s : List (Term (A:=A) (I:=I))) : total rel (s.reverse.map Term.flip)= -total rel s := by
  have hf (t : Term (A:=A) (I:=I)) : term rel t.flip= -term rel t := by
    obtain ⟨i,b,c⟩ := t
    cases b <;> simp [term,Term.flip]
  simp only [total,List.map_map,Function.comp_def,hf,List.map_reverse,List.sum_reverse,List.sum_neg]
variable (hz : ∀ts : List (Term (A:=A) (I:=I)),FreeGroup.mk (word rel ts)=1→total rel ts=0)
include hz in
lemma total_eq {s t : List (Term (A:=A) (I:=I))}
    (hst : FreeGroup.mk (word rel s)=FreeGroup.mk (word rel t)) : total rel s=total rel t := by
  have hword : FreeGroup.mk (word rel (s++t.reverse.map Term.flip))=1 := by
    rw [word_append,word_reverse_flip,←FreeGroup.mul_mk,←FreeGroup.inv_mk,hst,mul_inv_cancel]
  have h := hz _ hword
  rw [total_append,total_reverse_flip] at h
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)

def area (x : N rel) : CellModule.Module (G rel) I := total rel (Classical.choose (expansion rel x.property))
include hz in
lemma area_eq (x : N rel) (ts : List (Term (A:=A) (I:=I)))
    (hts : FreeGroup.mk (word rel ts)=x.val) : area rel x=total rel ts := by
  exact total_eq rel hz ((Classical.choose_spec (expansion rel x.property)).trans hts.symm)
include hz in
lemma area_mul (x y : N rel) : area rel (x*y)=area rel x+area rel y := by
  obtain ⟨s,hs⟩ := expansion rel x.property
  obtain ⟨t,ht⟩ := expansion rel y.property
  rw [area_eq rel hz x s hs,area_eq rel hz y t ht,area_eq rel hz (x*y) (s++t) (by
    rw [word_append,←FreeGroup.mul_mk,hs,ht];rfl),total_append]
include hz in
lemma area_one : area rel 1=0 := by
  exact (area_eq rel hz 1 [] rfl).trans rfl

def conjugate (w : FreeGroup A) (x : N rel) : N rel :=
  ⟨w*x.val*w⁻¹,(Subgroup.normalClosure_normal (s:=relations rel)).conj_mem _ x.property w⟩
def move (w : FreeGroup A) (t : Term (A:=A) (I:=I)) : Term (A:=A) (I:=I) :=
  ⟨t.index,t.positive,w.toWord++t.connector⟩
lemma move_mk (w : FreeGroup A) (t : Term (A:=A) (I:=I)) :
    FreeGroup.mk ((move w t).word rel)=w*FreeGroup.mk (t.word rel)*w⁻¹ := by
  simp only [move,Term.word,Term.core,←FreeGroup.mul_mk,←FreeGroup.inv_mk,FreeGroup.mk_toWord,mul_inv_rev]
  group
  rfl
lemma move_word (w : FreeGroup A) (ts : List (Term (A:=A) (I:=I))) :
    FreeGroup.mk (word rel (ts.map (move w)))=w*FreeGroup.mk (word rel ts)*w⁻¹ := by
  induction ts with
  | nil=>change (1 : FreeGroup A)=w*1*w⁻¹; simp
  | cons t ts ih=>
    change FreeGroup.mk ((move w t).word rel++word rel (ts.map (move w)))=
      w*FreeGroup.mk (t.word rel++word rel ts)*w⁻¹
    rw [←FreeGroup.mul_mk,move_mk,ih,←FreeGroup.mul_mk]
    group
lemma move_term (w : FreeGroup A) (t : Term (A:=A) (I:=I)) :
    term rel (move w t)=translate (q rel w) (term rel t) := by
  simp only [term,move,←FreeGroup.mul_mk,FreeGroup.mk_toWord,map_mul]
  split <;> simp only [translate_single,map_neg]
lemma move_total (w : FreeGroup A) (ts : List (Term (A:=A) (I:=I))) :
    total rel (ts.map (move w))=translate (q rel w) (total rel ts) := by
  simp only [total,List.map_map,Function.comp_def,move_term,map_list_sum]
include hz in
lemma area_conjugate (w : FreeGroup A) (x : N rel) :
    area rel (conjugate rel w x)=translate (q rel w) (area rel x) := by
  obtain ⟨s,hs⟩ := expansion rel x.property
  rw [area_eq rel hz x s hs,area_eq rel hz (conjugate rel w x) (s.map (move w)) (by
    rw [move_word,hs];rfl),move_total]

def d₂ : CellModule.Module (G rel) I→+CellModule.Module (G rel) A :=
  Finsupp.liftAddHom (fun p=>zmultiplesHom _ (translate p.1 (fox (q rel) (FreeGroup.mk (rel p.2)))))
@[simp] lemma d₂_single (p : G rel×I) (z : ℤ) :
    d₂ rel (Finsupp.single p z)=z • translate p.1 (fox (q rel) (FreeGroup.mk (rel p.2))) := by
  simp [d₂]
lemma d₂_translate (g : G rel) (x : CellModule.Module (G rel) I) :
    d₂ rel (translate g x)=translate g (d₂ rel x) := by
  induction x using Finsupp.induction_linear with
  | zero=>simp
  | add a b ha hb=>simp only [map_add,ha,hb]
  | single p z=>simp only [translate_single,d₂_single,map_zsmul,translate_mul]
lemma q_rel (i : I) : q rel (FreeGroup.mk (rel i))=1 := PresentedGroup.one_of_mem ⟨i,rfl⟩
lemma q_word (ts : List (Term (A:=A) (I:=I))) : q rel (FreeGroup.mk (word rel ts))=1 :=
  PresentedGroup.mk_eq_one_iff.mpr (word_mem rel ts)
lemma fox_conjugate (w r : FreeGroup A) (hr : q rel r=1) :
    fox (q rel) (w*r*w⁻¹)=translate (q rel w) (fox (q rel) r) := by
  rw [fox_mul,fox_mul,fox_inv,map_mul,hr,mul_one,map_neg,←translate_mul,mul_inv_cancel,translate_one]
  abel
lemma d₂_term (t : Term (A:=A) (I:=I)) : d₂ rel (term rel t)=fox (q rel) (FreeGroup.mk (t.word rel)) := by
  have hc : q rel (FreeGroup.mk (t.core rel))=1 := by
    cases hb : t.positive <;> simp only [Term.core,hb,Bool.false_eq_true,ite_false,ite_true,←FreeGroup.inv_mk,map_inv,q_rel,inv_one]
  rw [Term.word,←FreeGroup.mul_mk,←FreeGroup.mul_mk,←FreeGroup.inv_mk,fox_conjugate rel _ _ hc]
  cases hb : t.positive <;>
    simp only [term,Term.core,hb,Bool.false_eq_true,ite_false,ite_true,map_neg,d₂_single,one_zsmul,←FreeGroup.inv_mk,fox_inv,q_rel,inv_one,translate_one,map_neg]
lemma d₂_total (ts : List (Term (A:=A) (I:=I))) :
    d₂ rel (total rel ts)=fox (q rel) (FreeGroup.mk (word rel ts)) := by
  induction ts with
  | nil=>rfl
  | cons t ts ih=>
    change d₂ rel (term rel t+total rel ts)=fox (q rel) (FreeGroup.mk (t.word rel++word rel ts))
    rw [map_add,d₂_term,ih,←FreeGroup.mul_mk,fox_mul]
    have ht : q rel (FreeGroup.mk (t.word rel))=1 := by
      exact PresentedGroup.mk_eq_one_iff.mpr (term_mem rel t)
    rw [ht,translate_one]
lemma d₂_area (x : N rel) : d₂ rel (area rel x)=fox (q rel) x.val := by
  rw [area,d₂_total,Classical.choose_spec (expansion rel x.property)]
lemma boundary_d₂ (x : CellModule.Module (G rel) I) : boundary (q rel) (d₂ rel x)=0 := by
  induction x using Finsupp.induction_linear with
  | zero=>simp
  | add a b ha hb=>simp only [map_add,ha,hb,add_zero]
  | single p z=>rw [d₂_single,map_zsmul,boundary_translate,boundary_fox,q_rel,sub_self,map_zero,zsmul_zero]
end
end TorsionFreeZeroDivisors.RelationArea


end


end OAI
