import Mathlib
import OAI.Geometry.HyperbolicGroups.WordPicture
import OAI.Geometry.HyperbolicGroups.NormalFaceFilling
import OAI.Geometry.HyperbolicGroups.WordPictureArea

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm WordPictures
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Only locally PROVED fillings are admitted to this auxiliary relator set.
It is used for derivation substitution, not to alter either presentation. -/
def BoundedConeRelator : Set (List (Dart n w)) :=
  {r | ∃ k ≤ 30, Homotopy (SimpleWordRelator n w d) (r.flatMap (collapse n w)) [] k}

variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Dart n w)
  (closed : ∀ i, start n w (word (finRotate ell i)) = start n w (rev n w (word i)))
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (exteriorWalkTarget n w d ell hell word closed c hc f))
variable (hm : P.FrozenMapped (exteriorWalkFrozen n w d ell hell word closed c hc f))
  (hs : P.Simple) (hb : P.NoBigon)
variable (xs : List P.Dart) (hx : IsBoundary P.pairing.face xs)
  (hw : xs.map ((exteriorWalkTarget n w d ell hell word closed c hc f).label ∘ P.index) =
    List.ofFn word)
  (ht : ∀ x, (walkTarget n w d c hc f).isExterior ell hell word closed (P.index x) ↔ x ∈ xs)

/-- A normalized actual cone disk defines a word picture whose every interior
face has a proved cost30 replacement. The protected exterior is EXCLUDED. -/
def normalWordPicture : WordPicture (BoundedConeRelator n w d) (List.ofFn word) where
  Dart := P.Dart
  pairing := P.pairing
  genusZero := P.genusZero
  label := (exteriorWalkTarget n w d ell hell word closed c hc f).label ∘ P.index
  paired := P.paired
  outside := xs
  boundary := hx
  word := hw
  interior := by
    intro x hxo
    cases hi : P.index x with
    | inl s =>
      cases s with
      | inl s =>
        obtain ⟨ys,hys,hym,hfill⟩ := exterior_top_filling n w d ell hell word closed c hc f P hs hb
          x s.1 s.2 hi
        exact ⟨ys,hys,hym,Or.inl hfill⟩
      | inr s =>
        obtain ⟨ys,hys,hym,hfill⟩ := exterior_frozen_filling n w d ell hell word closed c hc f P hm x s hi
        exact ⟨ys,hys,hym,Or.inl hfill⟩
    | inr s =>
      have he : (walkTarget n w d c hc f).isExterior ell hell word closed (P.index x) := by
        rw [hi]; trivial
      exact False.elim (hxo ((ht x).mp he))

include hm hs hb xs hx hw ht in
/-- The genuine normalized cone disk costs at most
THIRTY times its number of INTERIOR cells in the finite simple presentation.
No bound on the number of diagram cells is assumed or claimed here. -/
theorem normal_disk_area :
    ∃ a, Homotopy (SimpleWordRelator n w d) ((List.ofFn word).flatMap (collapse n w)) [] a ∧
      (a : ℤ) ≤ 30 * (cycles P.pairing.face - 1) := by
  let Q := normalWordPicture n w d ell hell word closed c hc f P hm hs hb xs hx hw ht
  have ho : Q.outside ≠ [] := by
    intro he
    have hh := hw
    change xs = [] at he
    rw [he,List.map_nil] at hh
    have hl := congrArg List.length hh
    simp only [List.length_nil,List.length_ofFn] at hl
    omega
  obtain ⟨k,hk,he,hF⟩ := Q.filling_interior ho
  obtain ⟨a,ha,hfill⟩ := hk.substitute (collapse n w) (fun e => collapse_rev n w e)
    (fun r hr => hr)
  refine ⟨a,hfill,?_⟩
  have hb' : (a : ℤ) ≤ 30 * (k : ℤ) := by exact_mod_cast ha
  change (k : ℤ) + 1 ≤ cycles P.pairing.face at hF
  omega

end HyperbolicObstruction.ConeSkeleton
end

end OAI
