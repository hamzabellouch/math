import Mathlib
import OAI.Geometry.HyperbolicGroups.ExteriorTarget
import OAI.Geometry.HyperbolicGroups.PolygonBoundaryList
import OAI.Geometry.HyperbolicGroups.ConeExteriorWalk
import OAI.Geometry.HyperbolicGroups.BoundaryLift

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Dart n w)
  (closed : ∀ i, start n w (word (finRotate ell i)) = start n w (rev n w (word i)))
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)

lemma exteriorCellToWalk_exterior_iff
    (weight : Cell n w d → A)
    (P : CellPicture (exteriorCellTarget n w d ell hell word closed weight))
    (xs : List P.Dart)
    (hp : ∀ x, (boundary n w d).outsideTag ell hell word closed (P.index x) =
      if x ∈ xs then some true else none) :
    ∀ x, (walkTarget n w d c hc f).isExterior ell hell word closed
      ((exteriorCellToWalk n w d ell hell word closed c hc f weight P).index x) ↔ x ∈ xs := by
  intro x
  have ht : (walkTarget n w d c hc f).isExterior ell hell word closed
      ((exteriorCellToWalk n w d ell hell word closed c hc f weight P).index x) ↔
      (boundary n w d).outsideTag ell hell word closed (P.index x) ≠ none := by
    rcases hxi : P.index x with ⟨a,b,i⟩
    cases a with
    | inl a =>
      change (walkTarget n w d c hc f).isExterior ell hell word closed
        (exteriorCellStep n w d ell hell word closed c hc f (P.index x)) ↔ _
      rw [hxi]
      simp only [exteriorCellStep,WalkCellTarget.isExterior,Sum.elim_inl,
        PolygonTarget.Boundary.outsideTag,ne_eq,not_true_eq_false]
    | inr a =>
      change (walkTarget n w d c hc f).isExterior ell hell word closed
        (exteriorCellStep n w d ell hell word closed c hc f (P.index x)) ↔ _
      rw [hxi]
      simp only [exteriorCellStep,WalkCellTarget.isExterior,Sum.elim_inr,
        PolygonTarget.Boundary.outsideTag,ne_eq,Option.some_ne_none,not_false_eq_true]
  refine ht.trans ⟨?_, ?_⟩
  · intro h
    by_contra hnot
    exact h ((hp x).trans (ite_eq_right hnot))
  · intro h he
    exact (Option.some_ne_none true) (((hp x).trans (ite_eq_left h)).symm.trans he)

/-- Disk producer for the finite polygonal cone target:
a nonempty closed literal nullword has a genus-zero mixed picture in the
full normal form, with all outside positions and labels preserved. No
existence of a disk diagram, normal form, or boundary matching is assumed. -/
theorem nullWord_normal_picture
    (h : PresentedGroup.mk (FreeGroup.mk '' Set.range (boundary n w d).attachingWord)
      (FreeGroup.mk (List.ofFn word)) = 1) :
    ∃ (Q : WalkPicture.{0} (exteriorWalkTarget n w d ell hell word closed c hc f))
      (xs : List Q.Dart),
      Q.FrozenMapped (exteriorWalkFrozen n w d ell hell word closed c hc f) ∧
      Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective (isApex n w) ∧
      IsBoundary Q.pairing.face xs ∧
      xs.map ((exteriorWalkTarget n w d ell hell word closed c hc f).label ∘ Q.index) = List.ofFn word ∧
      (∀ x, (walkTarget n w d c hc f).isExterior ell hell word closed (Q.index x) ↔ x ∈ xs) ∧
      (∀ x s, Q.index x = .inr s → s.2.1 = true) := by
  let wt : Cell n w d → A := fun _ => 0
  obtain ⟨P,xs,hb,hl,ht⟩ := (boundary n w d).nullWord_picture ell hell word closed wt
    (isApex n w) (radial n w) rfl h
  let P' := exteriorCellToWalk n w d ell hell word closed c hc f wt P
  have hm := exteriorCellToWalk_frozen n w d ell hell word closed c hc f wt P
  have hp := exteriorCellToWalk_tag n w d ell hell word closed c hc f wt P xs ht
  have hk := exteriorCellToWalk_exterior_iff n w d ell hell word closed c hc f wt P xs ht
  obtain ⟨Q,⟨hr⟩,hqm,hqs,hqb,hqr,hqa,hchain⟩ :=
    (walkTarget n w d c hc f).normalize_exterior ell hell word closed
      (walkFrozenTarget n w d c hc f) P' hm hp (isApex n w) (radial n w)
  obtain ⟨ys,hy,he,hword,hkeep⟩ := hr.boundary
    ((walkTarget n w d c hc f).exterior_frozen ell hell word closed) xs hb hk
  refine ⟨Q,ys,hqm,hqs,hqb,hqr,hqa,hy,?_,hkeep,?_⟩
  · rw [hword]
    have hv : (exteriorWalkTarget n w d ell hell word closed c hc f).label ∘ P'.index =
        (exteriorCellTarget n w d ell hell word closed wt).edge ∘ P.index := by
      funext x
      exact exteriorCellStep_label n w d ell hell word closed c hc f _
    rw [hv]
    exact hl
  · intro x s hx
    apply hp (hr.map x) s
    rw [← hr.index]
    exact hx

end HyperbolicObstruction.ConeSkeleton
end

end OAI
