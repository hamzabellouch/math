import Mathlib
import OAI.Geometry.HyperbolicGroups.PolygonTarget
import OAI.Geometry.HyperbolicGroups.WordPicture
import OAI.Geometry.HyperbolicGroups.PolygonBoundaryList
import OAI.Geometry.HyperbolicGroups.PolygonDiskProducer
import OAI.Geometry.HyperbolicGroups.CellularFilling

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
open HyperbolicObstruction.PictureSwitch HyperbolicObstruction.WordPictures Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C A V : Type*} [Fintype C] (B : PolygonTarget.Boundary C (A × Bool) V)
variable (hinv : B.rev = invLetter)

omit [Fintype C] in
include hinv in
/-- Both literal orientations of every included polygon are available as
one relator face; indexed positions are retained even for repeated labels. -/
lemma relator_boundary {R : Set (Word A)} (c : C) (hc : B.attachingWord c ∈ R)
    (b : Bool) (i : Fin (B.size c)) :
    ∃ ys : List B.Side, IsBoundary B.next ys ∧ (⟨c,b,i⟩ : B.Side) ∈ ys ∧
      SymmetricRelator R (ys.map B.sideLabel) := by
  cases b with
  | true =>
    refine ⟨B.positiveSides c,B.positiveSides_boundary c,?_,Or.inl ?_⟩
    · exact List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
    · rwa [B.positiveSides_label]
  | false =>
    have hp := B.positiveSides_boundary c
    have hh : IsBoundary B.next ((B.positiveSides c).reverse.map B.opposite) := by
      apply hp.reverse.map B.opposite B.opposite.injective
      intro s
      simpa only [Perm.inv_def,Equiv.apply_symm_apply] using
        (congrArg B.next (B.reverse_next (B.next⁻¹ s))).symm
    refine ⟨(B.positiveSides c).reverse.map B.opposite,hh,?_,?_⟩
    · apply List.mem_map.mpr
      refine ⟨⟨c,true,i⟩,List.mem_reverse.mpr ?_,rfl⟩
      exact List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
    · have he : ((B.positiveSides c).reverse.map B.opposite).map B.sideLabel =
          FreeGroup.invRev ((B.positiveSides c).map B.sideLabel) := by
        simp only [List.map_map,List.map_reverse,FreeGroup.invRev,Function.comp_def,
          B.edge_opposite,hinv,invLetter]
      rw [he,B.positiveSides_label]
      exact symmetricRelator_inv (Or.inl hc)

variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → A × Bool)
  (closed : ∀ i, B.start (word (finRotate ell i)) = B.start (B.rev (word i)))
variable {M : Type*} [AddCommGroup M] (weight : C → M) (apex : V → Bool)
  (radial : ∀ l, apex (B.start l) = true → apex (B.start (B.rev l)) = false)
variable (P : CellPicture.{0} (B.outsideTarget ell hell word closed weight apex radial))

omit [Fintype C] in
include hinv in
/-- A genuine mapped polygon disk gives a counted derivation over EXACTLY
its original attaching words. The distinguished outside is excluded from
the relator list, so this is not the tautological exterior-relator argument. -/
theorem picture_filling (xs : List P.Dart) (hx : IsBoundary P.pairing.face xs)
    (hw : xs.map ((B.outsideTarget ell hell word closed weight apex radial).edge ∘ P.index) =
      List.ofFn word)
    (ht : ∀ x, B.outsideTag ell hell word closed (P.index x) =
      if x ∈ xs then some true else none) :
    ∃ k, Homotopy (Set.range B.attachingWord) (List.ofFn word) [] k ∧
      k ≤ Fintype.card P.Dart / 2 ∧ (k : ℤ) ≤ cycles P.pairing.face := by
  apply P.word_filling hinv xs hx hw
  intro x hxo
  have htag := ht x
  rw [ite_eq_right hxo] at htag
  rcases hi : P.index x with ⟨a,b,i⟩
  rw [hi] at htag
  cases a with
  | inl c =>
    have hr := (B.withOutside ell hell word closed).relator_boundary hinv
      (.inl c) (R := Set.range B.attachingWord) ⟨c,rfl⟩ b i
    convert hr using 1
    funext ys
    congr 2
  | inr a =>
    change some b = none at htag
    cases htag

end HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
end

end OAI
