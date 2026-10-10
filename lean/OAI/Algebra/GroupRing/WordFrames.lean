import Mathlib
import OAI.Algebra.GroupRing.WordLiftSurgery

namespace OAI



section
namespace TorsionFreeZeroDivisors.WordFrames
open scoped Classical
open WordBlocks WordCursor
noncomputable section
variable {A G : Type} [Group G] (v : A→G) (inv : A→A)
abbrev words (bs : List (G×List A)) : List (List A) := bs.map Prod.snd
def position : (bs : List (G×List A))→Occ (words bs)→G
  | [],i=>Empty.elim i
  | (g,w)::_bs,.inl i=>g*cursor v w i.val
  | (_g,_w)::bs,.inr i=>position bs i
structure Data (bs : List (G×List A)) where
  matching : Matching inv (words bs)
  lifted : Lift v matching
  framed : ∀i,lifted.position i=position v bs i
variable {v inv}
def Data.rename {bs cs : List (G×List A)} (d : Data v inv bs)
    (e : Occ (words bs)≃Occ (words cs))
    (hl : ∀i,letter (words cs) (e i)=letter (words bs) i)
    (hr : ∀i,e (BlockBoundary.rotation (lengths (words bs)) i)=BlockBoundary.rotation (lengths (words cs)) (e i))
    (hp : ∀i,position v cs (e i)=position v bs i) : Data v inv cs where
  matching := d.matching.rename e hl hr
  lifted := d.lifted.rename e hl hr
  framed i := by
    change d.lifted.position (e.symm i)=_
    rw [d.framed,←hp,Equiv.apply_symm_apply]
variable (hv : ∀a,v (inv a)=(v a)⁻¹) (hi : Function.Involutive inv)
def Data.removeCaps (g : G) (a : A) (w : List A) (bs : List (G×List A))
    (d : Data v inv ((g,a::(w++[inv a]))::bs)) : Data v inv ((g*v a,w)::bs) where
  matching := d.matching.removeCaps hi a w (words bs)
  lifted := d.lifted.removeCaps hv hi
  framed i := by
    change d.lifted.position (capEmbedding a w (words bs) i)=_
    rw [d.framed]
    cases i with
    | inl i=>
      change g*cursor v (a::(w++[inv a])) (i.val+1)=(g*v a)*cursor v w i.val
      rw [cursor_cons_succ,cursor_append_left v w [inv a] i.val i.isLt.le,mul_assoc]
    | inr i=>rfl
def focus : (pre : List (G×List A))→(g : G)→(w : List A)→(post : List (G×List A))→
    Occ (words (pre++(g,w)::post))≃Occ (words ((g,w)::(pre++post)))
  | [],_,_,_=>Equiv.refl _
  | t::pre,g,w,post=>(Equiv.sumCongr (Equiv.refl (Fin t.2.length)) (focus pre g w post)).trans exchange
omit [Group G] in
lemma focus_letter (pre : List (G×List A)) (g : G) (w : List A) (post : List (G×List A))
    (i : Occ (words (pre++(g,w)::post))) :
    letter (words ((g,w)::(pre++post))) (focus pre g w post i)=letter (words (pre++(g,w)::post)) i := by
  induction pre with
  | nil=>rfl
  | cons t pre ih=>
    cases i with
    | inl i=>rfl
    | inr i=>
      change Sum.elim w.get (Sum.elim t.2.get (letter (words (pre++post))))
        (exchange (.inr (focus pre g w post i)))=letter (words (pre++(g,w)::post)) i
      rw [exchange_letter]
      exact ih i
omit [Group G] in
lemma focus_rotation (pre : List (G×List A)) (g : G) (w : List A) (post : List (G×List A))
    (i : Occ (words (pre++(g,w)::post))) :
    focus pre g w post (BlockBoundary.rotation (lengths (words (pre++(g,w)::post))) i)=
      BlockBoundary.rotation (lengths (words ((g,w)::(pre++post)))) (focus pre g w post i) := by
  induction pre with
  | nil=>rfl
  | cons t pre ih=>
    cases i with
    | inl i=>rfl
    | inr i=>
      change exchange (.inr (focus pre g w post (BlockBoundary.rotation (lengths (words (pre++(g,w)::post))) i)))=
        Equiv.sumCongr (finRotate w.length)
          (Equiv.sumCongr (finRotate t.2.length) (BlockBoundary.rotation (lengths (words (pre++post)))))
          (exchange (.inr (focus pre g w post i)))
      rw [ih]
      exact exchange_rotation (finRotate t.2.length) (finRotate w.length) (BlockBoundary.rotation (lengths (words (pre++post)))) (.inr (focus pre g w post i))
lemma focus_position (pre : List (G×List A)) (g : G) (w : List A) (post : List (G×List A))
    (i : Occ (words (pre++(g,w)::post))) :
    position v ((g,w)::(pre++post)) (WordFrames.focus pre g w post i)=position v (pre++(g,w)::post) i := by
  induction pre with
  | nil=>rfl
  | cons t pre ih=>
    cases t with
    | mk g' w'=>
      cases i with
      | inl i=>rfl
      | inr i=>
        have hh := ih i
        change position v ((g,w)::(g',w')::(pre++post))
          (exchange (.inr (WordFrames.focus pre g w post i)))=position v (pre++(g,w)::post) i
        cases he : WordFrames.focus pre g w post i with
        | inl j=>rw [he] at hh; exact hh
        | inr j=>rw [he] at hh; exact hh
variable (v)
def Data.focus (pre : List (G×List A)) (g : G) (w : List A) (post : List (G×List A))
    (d : Data v inv (pre++(g,w)::post)) : Data v inv ((g,w)::(pre++post)) :=
  d.rename (WordFrames.focus pre g w post)
    (WordFrames.focus_letter _ _ _ _) (WordFrames.focus_rotation _ _ _ _) (focus_position pre g w post)
def Data.unfocus (pre : List (G×List A)) (g : G) (w : List A) (post : List (G×List A))
    (d : Data v inv ((g,w)::(pre++post))) : Data v inv (pre++(g,w)::post) :=
  d.rename (WordFrames.focus pre g w post).symm
    (fun x=>by simpa using (WordFrames.focus_letter pre g w post ((WordFrames.focus pre g w post).symm x)).symm)
    (fun x=>by
      apply (WordFrames.focus pre g w post).injective
      simpa only [Equiv.apply_symm_apply] using (WordFrames.focus_rotation pre g w post ((WordFrames.focus pre g w post).symm x)).symm)
    (fun x=>by simpa only [Equiv.apply_symm_apply] using
      (focus_position (v:=v) pre g w post ((WordFrames.focus pre g w post).symm x)).symm)
end
end TorsionFreeZeroDivisors.WordFrames

end



end OAI
