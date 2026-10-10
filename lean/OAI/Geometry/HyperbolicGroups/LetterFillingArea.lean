import Mathlib
import OAI.Geometry.HyperbolicGroups.LetterNormalPicture
import OAI.Geometry.HyperbolicGroups.NormalDiskArea

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch WordPictures
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)

/-- Connected quantitative output for the original null word:
a genuine protected normal disk AND a simple-relator filling bounded by
thirty times its actual interior face count. No linear bound on that face
count is assumed. -/
theorem null_letter_word_counted_normal_picture
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
      (∀ x s, Q.index x = .inr s → s.2.1 = true) ∧
      ∃ a, Homotopy (SimpleWordRelator n w d) (List.ofFn word) [] a ∧
        (a : ℤ) ≤ 30 * (cycles Q.pairing.face - 1) := by
  obtain ⟨Q,xs,hm,hs,hb,hr,hrad,hxs,hword,htag,hor⟩ :=
    null_letter_word_normal_picture n w d ell word hell c hc f h
  obtain ⟨a,hfill,ha⟩ := normal_disk_area n w d ell hell (letterDart n w ∘ word)
    (letterWordClosed n w ell word) c hc f Q hm hs hb xs hxs hword htag
  refine ⟨Q,xs,hm,hs,hb,hr,hrad,hxs,hword,htag,hor,a,?_,ha⟩
  have he : (List.ofFn (letterDart n w ∘ word)).flatMap (collapse n w) = List.ofFn word := by
    rw [← List.map_ofFn]
    exact collapse_letter_word n w (List.ofFn word)
  rwa [he] at hfill

end HyperbolicObstruction.ConeSkeleton
end

end OAI
