import Mathlib
import OAI.Algebra.GroupRing.FramedLoopIdentities
import OAI.Algebra.GroupRing.ConeSigned

namespace OAI



section
namespace TorsionFreeZeroDivisors.ConeArea
open scoped Classical BigOperators
open PortSubdivision GraphPresentation GraphConePresentation ConeSigned WordCursor
noncomputable section
variable {V D S : Type} (Γ : PortGraph V D) (R : Routes Γ) (label : D→S×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
local notation "letters" => freeLetter ∘ label
local notation "G" => GraphConePresentation.Group Γ letters R
local notation "v" => ConeSigned.eval Γ R label ∘ ConeSigned.labels Γ R label
local notation "c" => ConeChains.coneCharge Γ R label freeLetter
include hl in
lemma letters_reverse (d : D) : letters (Γ.reverse d)=(letters d)⁻¹ := by
  simp only [Function.comp_apply,hl,freeLetter_inverse]
lemma path_value {a b : V} (p : Path (ConePicture.graph Γ R) a b) :
    value v p.darts=PresentedGroup.mk _ (p.eval (ConePicture.wordLabel Γ R letters)) := by
  induction p with
  | nil=>simp [Path.darts_nil]
  | cons d p ih=>
    rw [Path.darts_cons,value_cons,ih,Path.eval_cons,map_mul]
    congr 1
    exact congrArg (PresentedGroup.mk _) (wordLabel_eq Γ R label d)
lemma root_value (a : V) : value v (ConePicture.rootPath Γ R a).darts=radialValue Γ letters R a := by
  rw [path_value,ConePicture.rootPath_eval]
  rfl
lemma root_charge (g : G) (a : V) :
    PathCharges.charge v c g (ConePicture.rootPath Γ R a).darts=0 := by
  by_cases ha : a=R.base a
  · simp only [ConePicture.rootPath,dite_eq_left ha,Path.darts_cast,Path.darts_nil,PathCharges.charge_nil]
  · simp only [ConePicture.rootPath,dite_eq_right ha,Path.darts_cast,Path.single,Path.darts_cons,
      Path.darts_nil,PathCharges.charge_cons,PathCharges.charge_nil,ConeChains.coneCharge,add_zero]
include hl in
lemma eval_reverse (d : ConePicture.Dart Γ R) :
    v ((ConePicture.graph Γ R).reverse d)=(v d)⁻¹ := by
  dsimp only [Function.comp_apply]
  rw [ConeSigned.labels_reverse Γ R label hl,ConeSigned.eval_inverse]
include hl in
lemma charge_reverse (g : G) (d : ConePicture.Dart Γ R) :
    c (g*v d) ((ConePicture.graph Γ R).reverse d)=-c g d := by
  change c (g*ConeSigned.eval Γ R label (pack Γ R (ConePicture.labels Γ R label d))) _=_
  rw [eval_pack]
  exact ConeChains.coneCharge_reverse Γ R label WordPairing.inverseLetter freeLetter hl freeLetter_inverse g d
include hl in
lemma reverse_root_charge (g : G) (a : V) :
    PathCharges.charge v c g (ConePicture.rootPath Γ R a).reverse.darts=0 := by
  let w := (ConePicture.rootPath Γ R a).darts
  have h := PathCharges.charge_reverse v c (ConePicture.graph Γ R).reverse
    (eval_reverse Γ R label hl) (charge_reverse Γ R label hl) (g*(value v w)⁻¹) w
  rw [inv_mul_cancel_right,root_charge,neg_zero] at h
  simpa only [Path.darts_reverse] using h
include hl in
lemma triangle_charge (g : G) (d : D) :
    PathCharges.charge v c g (ConePicture.trianglePath Γ R d).darts=
      ConeChains.charge Γ R label freeLetter (g*radialValue Γ letters R (Γ.origin d)) d := by
  simp only [ConePicture.trianglePath,Path.darts_cast,Path.darts_append,PathCharges.charge_append]
  rw [root_charge,zero_add,root_value]
  rw [reverse_root_charge Γ R label hl,add_zero]
  simp only [Path.single,Path.darts_cons,Path.darts_nil,PathCharges.charge_cons,
    PathCharges.charge_nil,add_zero,ConeChains.coneCharge]
def loops (e : Edge Γ) : InitialPicture.Loop (ConePicture.graph Γ R) :=
  ⟨R.base (Γ.origin (representative Γ e)),ConePicture.trianglePath Γ R (representative Γ e)⟩
def words : Edge Γ→List (Generator (S:=S) Γ R × Bool) :=
  InitialPicture.relWords (ConePicture.graph Γ R) (ConeSigned.labels Γ R label) (loops Γ R)
include hl in
lemma words_mk (e : Edge Γ) : FreeGroup.mk (words Γ R label e)=attachment Γ letters R e := by
  rw [words,InitialPicture.relWords,Path.letters_mk]
  have hh : (fun d=>FreeGroup.mk [ConeSigned.labels Γ R label d])=ConePicture.wordLabel Γ R letters := by
    funext d;exact wordLabel_eq Γ R label d
  rw [hh]
  exact ConePicture.trianglePath_eval Γ R letters (letters_reverse Γ label hl) (representative Γ e)
include hl in
lemma loop_value (e : Edge Γ) : value v (loops Γ R e).2.darts=1 := by
  rw [path_value]
  change PresentedGroup.mk _ ((ConePicture.trianglePath Γ R (representative Γ e)).eval _)=1
  rw [ConePicture.trianglePath_eval Γ R letters (letters_reverse Γ label hl)]
  exact triangle_trivial Γ letters R (letters_reverse Γ label hl) _
include hl in
lemma loop_charge (g : G) (e : Edge Γ) :
    PathCharges.charge v c g (loops Γ R e).2.darts=Finsupp.single (g,e) (1:ℤ) := by
  rw [loops,triangle_charge Γ R label hl,ConeChains.charge]
  have he : edge Γ (representative Γ e)=e := ConeChains.representative_edge Γ e
  rw [he,ite_eq_left rfl]
  congr 1
  apply Prod.ext
  · exact mul_inv_cancel_right _ _
  · exact he
include hl in
lemma signed_charge (g : G) (t : AlgebraicPictures.Term (A:=Generator (S:=S) Γ R) (I:=Edge Γ)) :
    PathCharges.charge v c g (InitialPicture.signedLoop (ConePicture.graph Γ R) (loops Γ R) t).2.darts=
      if t.positive then Finsupp.single (g,t.index) (1:ℤ) else -Finsupp.single (g,t.index) (1:ℤ) := by
  obtain ⟨i,b,co⟩ := t
  cases b
  · change PathCharges.charge v c g (loops Γ R i).2.reverse.darts= -Finsupp.single (g,i) (1:ℤ)
    rw [Path.darts_reverse]
    have h := PathCharges.charge_reverse v c (ConePicture.graph Γ R).reverse
      (eval_reverse Γ R label hl) (charge_reverse Γ R label hl) g (loops Γ R i).2.darts
    rw [loop_value Γ R label hl,mul_one,loop_charge Γ R label hl] at h
    exact h
  · exact loop_charge Γ R label hl g i
include hl in
lemma term_value (t : AlgebraicPictures.Term (A:=Generator (S:=S) Γ R) (I:=Edge Γ)) :
    value (ConeSigned.eval Γ R label) (t.word (words Γ R label))=1 := by
  rw [AlgebraicPictures.Term.word,value_append,value_append]
  have hr : value (ConeSigned.eval Γ R label) (words Γ R label t.index)=1 := by
    rw [eval_value,words_mk Γ R label hl]
    exact PresentedGroup.one_of_mem ⟨_,rfl⟩
  have hi (w) := PathCharges.value_reverse (ConeSigned.eval Γ R label)
    WordPairing.inverseLetter (ConeSigned.eval_inverse Γ R label) w
  have hh (w : List (Generator (S:=S) Γ R × Bool)) : FreeGroup.invRev w=w.reverse.map WordPairing.inverseLetter := by
    simp only [FreeGroup.invRev,List.map_reverse]
    congr 1
  rw [hh,hi]
  cases hb : t.positive <;>
    simp only [AlgebraicPictures.Term.core,hb,Bool.false_eq_true,ite_false,ite_true,hh,hi,hr,inv_one,mul_one,mul_inv_cancel]
def termArea (t : AlgebraicPictures.Term (A:=Generator (S:=S) Γ R) (I:=Edge Γ)) :
    ConeChains.TwoChain Γ R label freeLetter :=
  if t.positive then Finsupp.single (PresentedGroup.mk _ (FreeGroup.mk t.connector),t.index) 1
  else -Finsupp.single (PresentedGroup.mk _ (FreeGroup.mk t.connector),t.index) 1
include hl in
lemma termArea_eq (t : AlgebraicPictures.Term (A:=Generator (S:=S) Γ R) (I:=Edge Γ)) :
    termArea Γ R label t=FramedLoopIdentities.area (ConePicture.graph Γ R)
      (ConeSigned.labels Γ R label) (loops Γ R) (ConeSigned.eval Γ R label) c t := by
  rw [FramedLoopIdentities.area,signed_charge Γ R label hl,eval_value]
  rfl
include hl in
/-- Every actual free identity of the physical triangular presentation has zero
integral translated physical-cell area. No cellular realization is presumed. -/
theorem identity_zero
    (hex : ∀{P : Type}[Fintype P][Nonempty P]
      (a : SphericalPicture.Data (O:=P) Γ label WordPairing.inverseLetter),¬a.Reduced)
    (ts : List (AlgebraicPictures.Term (A:=Generator (S:=S) Γ R) (I:=Edge Γ)))
    (he : FreeGroup.mk (AlgebraicPictures.word (words Γ R label) ts)=1) :
    (ts.map (termArea Γ R label)).sum=0 := by
  have hh := FramedLoopIdentities.identity_area_zero (ConePicture.graph Γ R)
    (ConeSigned.labels Γ R label) (ConeSigned.labels_reverse Γ R label hl) (loops Γ R)
    (ConeSigned.eval Γ R label) (ConeSigned.eval_inverse Γ R label) c
    (charge_reverse Γ R label hl) ts he (fun t _=>term_value Γ R label hl t)
    (fun a=>ConeSigned.reduces_to_empty Γ R label hl hex a)
  have heq : termArea Γ R label=FramedLoopIdentities.area (ConePicture.graph Γ R)
      (ConeSigned.labels Γ R label) (loops Γ R) (ConeSigned.eval Γ R label) c := by
    funext t;exact termArea_eq Γ R label hl t
  rw [heq];exact hh
end
end TorsionFreeZeroDivisors.ConeArea

end

end OAI
