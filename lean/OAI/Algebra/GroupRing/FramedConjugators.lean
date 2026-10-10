import Mathlib
import OAI.Algebra.GroupRing.WordFrames

namespace OAI



section
namespace TorsionFreeZeroDivisors.WordFrames
open scoped Classical
open WordBlocks WordCursor FreeGroup AlgebraicPictures
noncomputable section
variable {A G : Type} [Group G] (v : A×Bool→G)
  (hv : ∀a,v (WordPairing.inverseLetter a)=(v a)⁻¹)
def Data.removeConjugator (g : G) (c w : List (A×Bool)) (bs : List (G×List (A×Bool)))
    (d : Data v WordPairing.inverseLetter ((g,c++w++invRev c)::bs)) :
    Data v WordPairing.inverseLetter ((g*value v c,w)::bs) := by
  induction c generalizing g with
  | nil=>simpa only [List.nil_append,invRev_empty,List.append_nil,value_nil,mul_one] using d
  | cons a c ih=>
    have he : (a::c)++w++invRev (a::c)=a::((c++w++invRev c)++[WordPairing.inverseLetter a]) := by
      simp only [List.cons_append,invRev,WordPairing.inverseLetter,
        List.reverse_cons,List.map_cons,List.append_assoc]
    rw [he] at d
    have dd := d.removeCaps hv WordPairing.inverseLetter_involutive g a (c++w++invRev c) bs
    have ee := ih (g*v a) dd
    simpa only [value_cons,mul_assoc] using ee
def Data.removeConjugatorAt (g : G) (c w : List (A×Bool)) (pre post : List (G×List (A×Bool)))
    (d : Data v WordPairing.inverseLetter (pre++(g,c++w++invRev c)::post)) :
    Data v WordPairing.inverseLetter (pre++(g*value v c,w)::post) :=
  ((d.focus v pre g (c++w++invRev c) post).removeConjugator v hv g c w (pre++post)).unfocus v pre (g*value v c) w post
variable {I : Type} (rel : I→List (A×Bool))
def framedCores (ts : List (Term (A:=A) (I:=I))) : List (G×List (A×Bool)) :=
  ts.map (fun t=>(value v t.connector,t.core rel))
def framedWords (ts : List (Term (A:=A) (I:=I))) : List (G×List (A×Bool)) :=
  ts.map (fun t=>(1,t.word rel))
def Data.strip (ts : List (Term (A:=A) (I:=I))) (pre : List (G×List (A×Bool)))
    (d : Data v WordPairing.inverseLetter (pre++framedWords (G:=G) rel ts)) :
    Data v WordPairing.inverseLetter (pre++framedCores v rel ts) := by
  induction ts generalizing pre with
  | nil=>exact d
  | cons t ts ih=>
    change Data v WordPairing.inverseLetter
      (pre++(1,t.connector++t.core rel++invRev t.connector)::framedWords (G:=G) rel ts) at d
    have d' := d.removeConjugatorAt v hv 1 t.connector (t.core rel) pre (framedWords (G:=G) rel ts)
    rw [one_mul] at d'
    have d'' := ih (pre++[(value v t.connector,t.core rel)])
      (by simpa only [List.append_assoc,List.singleton_append] using d')
    simpa only [framedCores,List.map_cons,List.append_assoc,List.singleton_append] using d''
lemma flat_position (bs : List (G×List (A×Bool))) (h : ∀b∈bs,value v b.2=1) (hg : ∀b∈bs,b.1=1)
    (i : Occ (words bs)) :
    cursor v (words bs).flatten (coordinates (words bs) i).val=position v bs i := by
  induction bs with
  | nil=>exact Empty.elim i
  | cons b bs ih=>
    cases b with
    | mk g w=>
      have hg' := hg (g,w) (List.mem_cons_self)
      have hw := h (g,w) (List.mem_cons_self)
      change g=1 at hg'
      change value v w=1 at hw
      cases i with
      | inl i=>
        change cursor v (w++(words bs).flatten) i.val=g*cursor v w i.val
        rw [cursor_append_left v _ _ _ i.isLt.le,hg',one_mul]
      | inr i=>
        change cursor v (w++(words bs).flatten) (w.length+(coordinates (words bs) i).val)=position v bs i
        rw [cursor_append_right,hw,one_mul]
        exact ih (fun b hb=>h b (List.mem_cons_of_mem _ hb)) (fun b hb=>hg b (List.mem_cons_of_mem _ hb)) i
include hv in
lemma of_identity (bs : List (G×List (A×Bool)))
    (he : FreeGroup.mk (words bs).flatten=1) (h : ∀b∈bs,value v b.2=1) (hg : ∀b∈bs,b.1=1) :
    Nonempty (Data v WordPairing.inverseLetter bs) := by
  obtain ⟨d,hd⟩ := WordCursor.of_identity v hv he
  have hh : ∀w∈words bs,value v w=1 := by
    intro w hw
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
    exact h b hb
  refine ⟨⟨WordBlocks.ofDisk (words bs) d,WordBlocks.liftOfDisk d hd hh,?_⟩⟩
  exact flat_position v bs h hg
include hv in
/-- Every literal free identity among the conjugated relators gives a genuine
planar matching on the signed CORE words, retaining the actual conjugating
group coordinate at EVERY occurrence. No expected relator-area identity is
used as an assumption. -/
theorem identity_framed_cores (ts : List (Term (A:=A) (I:=I)))
    (he : FreeGroup.mk (AlgebraicPictures.word rel ts)=1)
    (ht : ∀t∈ts,value v (t.word rel)=1) :
    Nonempty (Data v WordPairing.inverseLetter (framedCores v rel ts)) := by
  have hw : words (framedWords (G:=G) rel ts)=ts.map (Term.word rel) := by
    simp only [words,framedWords,List.map_map]
    rfl
  obtain ⟨d⟩ := of_identity v hv (framedWords (G:=G) rel ts) (by
    rw [hw]
    simpa only [List.flatMap_def,AlgebraicPictures.word] using he) (by
      rintro b hb
      obtain ⟨t,ht',rfl⟩ := List.mem_map.mp hb
      exact ht t ht') (by
      rintro b hb
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp hb
      rfl)
  exact ⟨d.strip v hv rel ts []⟩
end
end TorsionFreeZeroDivisors.WordFrames

end



end OAI
