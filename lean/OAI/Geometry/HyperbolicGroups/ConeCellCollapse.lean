import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeTopCollapse
import OAI.Geometry.HyperbolicGroups.ConePresentationGroup
import OAI.Geometry.HyperbolicGroups.WordSubstitution

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma square_collapsedBoundary (s : Square n w) :
    collapsedBoundary n w d (.inr (.inr (.inl s))) =
      literalSquare n (extendRow n (.inr (.inr s.1)) s.2.val) s.1 := by
  rfl

lemma six_collapsedBoundary (s : Six n d) :
    collapsedBoundary n w d (.inr (.inr (.inr s))) = List.ofFn s.val := by
  rfl

/-- Uniform factor 30 for every actual bounded normal-form cell. The
fan paths, macro walk, exceptional loose edge and both decoration families
have all been expanded literally into the finite simple-cycle presentation. -/
theorem cell_collapse_filling (a : Cell n w d) :
    ∃ k ≤ 30, WordPictures.Homotopy (SimpleWordRelator n w d)
      (collapsedBoundary n w d a) [] k := by
  rcases a with f | (a | (s | s))
  · obtain ⟨k,hk,hh⟩ := fan_collapse_filling n w d f
    exact ⟨k,by omega,hh⟩
  · exact top_collapse_filling n w d a
  · rw [square_collapsedBoundary]
    have hp : w (TableModel.row rowSupport (extendRow n (.inr (.inr s.1)) s.2.val)
        (.inr (.inr s.1))) = true := by
      simpa only [row_extend] using s.2.property
    refine ⟨1,by decide,?_⟩
    simpa only [List.nil_append,List.append_nil] using
      WordPictures.Homotopy.move (WordPictures.Move.face [] [] _
        (SimpleWordRelator.square _ s.1 hp))
  · rw [six_collapsedBoundary]
    refine ⟨1,by decide,?_⟩
    simpa only [List.nil_append,List.append_nil] using
      WordPictures.Homotopy.move (WordPictures.Move.face [] [] _
        (SimpleWordRelator.six s.val s.property))

lemma collapse_letter_word (z : List (Alphabet n)) :
    (z.map (letterDart n w)).flatMap (collapse n w) = z := by
  induction z with
  | nil => rfl
  | cons a z ih => simp only [List.map_cons,List.flatMap_cons,collapse_letter,List.singleton_append,ih]

/-- Quantitative replacement of a literal polygon word derivation. This is
an algebraic substitution theorem, not an assumed bound on disk production. -/
theorem polygon_filling_to_simple {z : List (Alphabet n)} {k : ℕ}
    (h : WordPictures.Homotopy (Set.range (boundary n w d).attachingWord)
      (z.map (letterDart n w)) [] k) :
    ∃ a ≤ 30*k, WordPictures.Homotopy (SimpleWordRelator n w d) z [] a := by
  have hs : ∀ r ∈ Set.range (boundary n w d).attachingWord,
      ∃ a ≤ 30, WordPictures.Homotopy (SimpleWordRelator n w d) (r.flatMap (collapse n w)) [] a := by
    rintro r ⟨c,rfl⟩
    exact cell_collapse_filling n w d c
  obtain ⟨a,ha,hh⟩ := h.substitute (collapse n w) (fun e => collapse_rev n w e) hs
  exact ⟨a,ha,by simpa only [collapse_letter_word,List.flatMap_nil] using hh⟩

/-- The cone-polygon comparison creates no new relations among original
letters. Combined with the opposite implication, it is an exact null-word
equivalence in the original marked presentation, not a surjection claim. -/
theorem nullWord_polygon_iff (z : List (Alphabet n)) :
    PresentedGroup.mk (FreeGroup.mk '' Set.range (boundary n w d).attachingWord)
      (FreeGroup.mk (z.map (letterDart n w))) = 1 ↔
    PresentedGroup.mk (Relator n w d) (FreeGroup.mk z) = 1 := by
  constructor
  · intro hz
    obtain ⟨k,hk⟩ := WordPictures.existence (z.map (letterDart n w)) hz
    obtain ⟨a,ha,hh⟩ := polygon_filling_to_simple n w d hk
    have he := WordPictures.sound hh
    apply PresentedGroup.mk_eq_one_iff.mpr
    have hm := PresentedGroup.mk_eq_one_iff.mp he
    rw [simple_presentation_normalClosure] at hm
    exact hm
  · exact nullWord_to_polygon n w d z

end HyperbolicObstruction.ConeSkeleton
end

end OAI
