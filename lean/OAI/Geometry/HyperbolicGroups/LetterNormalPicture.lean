import Mathlib
import OAI.Geometry.HyperbolicGroups.ConePresentationGroup
import OAI.Geometry.HyperbolicGroups.ConeDiskNormal

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (word : Fin ell → Alphabet n)

theorem letterWordClosed : ∀ i,
    start n w ((letterDart n w ∘ word) (finRotate ell i)) =
    start n w (rev n w ((letterDart n w ∘ word) i)) := by
  intro i
  exact (start_letter n w _).trans (start_letter n w (inverseLetter n _)).symm

variable (hell : 0 < ell)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)

/-- Diagram existence and normalization for the original letter
presentation, not merely for a surrogate cone presentation. All literal
outside positions survive. Every mixed interior face maps to an actual
included source row, and no injectivity of random letter labels is assumed. -/
theorem null_letter_word_normal_picture
    (h : PresentedGroup.mk (Relator n w d) (FreeGroup.mk (List.ofFn word)) = 1) :
    ∃ (Q : WalkPicture.{0} (exteriorWalkTarget n w d ell hell (letterDart n w ∘ word)
        (letterWordClosed n w ell word) c hc f)) (xs : List Q.Dart),
      Q.FrozenMapped (exteriorWalkFrozen n w d ell hell (letterDart n w ∘ word)
        (letterWordClosed n w ell word) c hc f) ∧
      Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective (isApex n w) ∧
      IsBoundary Q.pairing.face xs ∧
      xs.map ((exteriorWalkTarget n w d ell hell (letterDart n w ∘ word)
        (letterWordClosed n w ell word) c hc f).label ∘ Q.index) =
        List.ofFn (letterDart n w ∘ word) ∧
      (∀ x, (walkTarget n w d c hc f).isExterior ell hell (letterDart n w ∘ word)
        (letterWordClosed n w ell word) (Q.index x) ↔ x ∈ xs) ∧
      (∀ x s, Q.index x = .inr s → s.2.1 = true) := by
  apply nullWord_normal_picture n w d ell hell (letterDart n w ∘ word)
    (letterWordClosed n w ell word) c hc f
  have hh := nullWord_to_polygon n w d (List.ofFn word) h
  simpa only [List.map_ofFn] using hh

end HyperbolicObstruction.ConeSkeleton
end

end OAI
