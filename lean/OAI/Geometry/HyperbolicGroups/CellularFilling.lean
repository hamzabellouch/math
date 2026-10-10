import Mathlib
import OAI.Geometry.HyperbolicGroups.NormalCell
import OAI.Geometry.HyperbolicGroups.WordPicture
import OAI.Geometry.HyperbolicGroups.IndexedBoundaryPullback
import OAI.Geometry.HyperbolicGroups.WordPictureFilling

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch.CellPicture
open HyperbolicObstruction.WordPictures Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {S A V B : Type*} [DecidableEq S] [AddCommMonoid B]
variable {T : CellTarget S (A × Bool) V B}
variable (P : CellPicture.{0} T) (hinv : T.rev = invLetter)
variable {R : Set (Word A)} {w : Word A}

/-- Reverse bridge from a literal genus-zero target-cell diagram to an
area-counted word picture. Every local premise is an actual attaching
polygon membership, not a filling or diagram-existence assumption. -/
def wordPicture (xs : List P.Dart) (hx : IsBoundary P.pairing.face xs)
    (hw : xs.map (T.edge ∘ P.index) = w)
    (hr : ∀ x, x ∉ xs → ∃ ys : List S, IsBoundary T.next ys ∧
      P.index x ∈ ys ∧ SymmetricRelator R (ys.map T.edge)) : WordPicture R w where
  Dart := P.Dart
  pairing := P.pairing
  genusZero := P.genusZero
  label := T.edge ∘ P.index
  paired := fun x => by rw [Function.comp_apply,Function.comp_apply,← hinv]; exact P.respects.2 x
  outside := xs
  boundary := hx
  word := hw
  interior := by
    intro x hxo
    obtain ⟨ys,ht,hy,hR⟩ := hr x hxo
    obtain ⟨zs,hz,hzm,hmap⟩ := P.mapped.pullback_boundary x ht hy
    refine ⟨zs,hz,hzm,?_⟩
    have he : zs.map (T.edge ∘ P.index) = ys.map T.edge := by rw [← hmap,List.map_map]
    rw [he]
    exact hR

include hinv in
/-- Quantitative extraction of a mapped genus-zero disk. Costs count real
relator moves, including inverse orientations, in the original word alphabet. -/
theorem word_filling (xs : List P.Dart) (hx : IsBoundary P.pairing.face xs)
    (hw : xs.map (T.edge ∘ P.index) = w)
    (hr : ∀ x, x ∉ xs → ∃ ys : List S, IsBoundary T.next ys ∧
      P.index x ∈ ys ∧ SymmetricRelator R (ys.map T.edge)) :
    ∃ k, Homotopy R w [] k ∧ k ≤ Fintype.card P.Dart / 2 ∧
      (k : ℤ) ≤ cycles P.pairing.face :=
  (P.wordPicture hinv xs hx hw hr).filling

end HyperbolicObstruction.PictureSwitch.CellPicture
end

end OAI
