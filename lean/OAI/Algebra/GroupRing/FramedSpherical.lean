import Mathlib
import OAI.Algebra.GroupRing.WordFrames
import OAI.Algebra.GroupRing.PictureChains

namespace OAI



section
namespace TorsionFreeZeroDivisors.WordFrames
open scoped Classical BigOperators
open WordBlocks WordCursor PortSubdivision
noncomputable section
variable {V D A G : Type} [Group G] (Γ : PortGraph V D) (lab : D→A) (v : A→G) (inv : A→A)
def mapLabels (bs : List (G×List D)) : List (G×List A) := bs.map (fun b=>(b.1,b.2.map lab))
def labelCoordinates : (bs : List (G×List D))→Occ (words bs)≃Occ (words (mapLabels lab bs))
  | []=>Equiv.refl _
  | b::bs=>Equiv.sumCongr (finCongr (List.length_map (f:=lab) (as:=b.2)).symm) (labelCoordinates bs)
omit [Group G] in
lemma labelCoordinates_letter (bs : List (G×List D)) (i : Occ (words bs)) :
    letter (words (mapLabels lab bs)) (labelCoordinates lab bs i)=lab (letter (words bs) i) := by
  induction bs with
  | nil=>exact Empty.elim i
  | cons b bs ih=>
    cases i with
    | inl i=>exact List.getElem_map _
    | inr i=>exact ih i
omit [Group G] in
lemma labelCoordinates_rotation (bs : List (G×List D)) (i : Occ (words bs)) :
    labelCoordinates lab bs (BlockBoundary.rotation (lengths (words bs)) i)=
      BlockBoundary.rotation (lengths (words (mapLabels lab bs))) (labelCoordinates lab bs i) := by
  induction bs with
  | nil=>exact Empty.elim i
  | cons b bs ih=>
    cases i with
    | inl i=>exact congrArg Sum.inl (rotate_cast (List.length_map (f:=lab) (as:=b.2)).symm i)
    | inr i=>exact congrArg Sum.inr (ih i)
lemma cursor_map (w : List D) (n : ℕ) : cursor v (w.map lab) n=cursor (v∘lab) w n := by
  simp only [cursor,value,←List.map_take,List.map_map]
lemma labelCoordinates_position (bs : List (G×List D)) (i : Occ (words bs)) :
    position v (mapLabels lab bs) (labelCoordinates lab bs i)=position (v∘lab) bs i := by
  induction bs with
  | nil=>exact Empty.elim i
  | cons b bs ih=>
    cases b with
    | mk g w=>
      cases i with
      | inl i=>exact congrArg (g*·) (cursor_map lab v w i.val)
      | inr i=>exact ih i
variable {v inv lab} {bs : List (G×List D)}
  (d : Data v inv (mapLabels lab bs)) (hc : AllClosed Γ (words bs))
def spherical : SphericalPicture.Data (O:=Occ (words bs)) Γ lab inv where
  rotation := BlockBoundary.rotation (lengths (words bs))
  partner := (labelCoordinates lab bs).symm.permCongr d.matching.partner
  involutive := PermutationTransport.involutive _ _ d.matching.involutive
  fixed_free := PermutationTransport.fixed_free _ _ d.matching.fixed_free
  dart := letter (words bs)
  consistent := closed_consistent Γ (words bs) hc
  compatible i := by
    rw [←labelCoordinates_letter lab bs,←labelCoordinates_letter lab bs]
    simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
    exact d.matching.compatible (labelCoordinates lab bs i)
  genusZero := by
    have hh := MapConjugation.genusZero (labelCoordinates lab bs).symm _ _ d.matching.genusZero
    have he : (labelCoordinates lab bs).symm.permCongr
        (BlockBoundary.rotation (lengths (words (mapLabels lab bs))))=BlockBoundary.rotation (lengths (words bs)) := by
      apply Equiv.ext
      intro i
      apply (labelCoordinates lab bs).injective
      simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
      exact (labelCoordinates_rotation lab bs i).symm
    rwa [he] at hh
def sphericalLift : PictureChains.Lift Γ lab inv v (spherical Γ d hc) where
  position i := d.lifted.position (labelCoordinates lab bs i)
  next i := by
    change d.lifted.position (labelCoordinates lab bs (BlockBoundary.rotation (lengths (words bs)) i))=_
    rw [labelCoordinates_rotation,d.lifted.next,labelCoordinates_letter]
    rfl
  pair i := by
    change d.lifted.position (labelCoordinates lab bs (((labelCoordinates lab bs).symm.permCongr d.matching.partner) i))=_
    simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
    rw [d.lifted.pair,labelCoordinates_letter]
    rfl
lemma sphericalLift_position (i : Occ (words bs)) :
    (sphericalLift Γ d hc).position i=position (v∘lab) bs i := by
  change d.lifted.position (labelCoordinates lab bs i)=_
  rw [d.framed,labelCoordinates_position]
variable {M : Type} [AddCommGroup M]
  (hv : ∀a,v (inv a)=(v a)⁻¹) (hl : ∀b,lab (Γ.reverse b)=inv (lab b))
  (c : G→D→M) (hcharge : ∀g b,c (g*v (lab b)) (Γ.reverse b)=-c g b)
include hv hl hcharge in
/-- Relator frames retain their ACTUAL conjugating coordinates when the
matching is interpreted as a spherical graph picture. -/
theorem charge_zero (hred : SphericalPicture.ReducesToEmpty Γ lab inv (spherical Γ d hc)) :
    (∑i : Occ (words bs),c (position (v∘lab) bs i) (letter (words bs) i))=0 := by
  have hh := PictureChains.chain_eq_zero hv hl (spherical Γ d hc) (sphericalLift Γ d hc) c hcharge hred
  simpa only [PictureChains.chain,sphericalLift_position,spherical] using hh
end
end TorsionFreeZeroDivisors.WordFrames

end



end OAI
