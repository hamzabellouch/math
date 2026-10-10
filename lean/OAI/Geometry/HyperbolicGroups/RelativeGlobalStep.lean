import Mathlib
import OAI.Geometry.HyperbolicGroups.NormalDiskArea
import OAI.Geometry.HyperbolicGroups.RelativeInteriorCount

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm WordPictures
open scoped BigOperators
open Occurrences.Shape
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))
variable (xs : List P.Dart) (hx : IsBoundary P.pairing.face xs)
  (hw : xs.map ((target n w d ell hell word c hc f).label ∘ P.index) =
    List.ofFn (letterDart n w ∘ word))
  (ht : ∀ x, (walkTarget n w d c hc f).isExterior ell hell (letterDart n w ∘ word)
    (letterWordClosed n w ell word) (P.index x) ↔ x ∈ xs)
variable {I : Type*} [Fintype I] (part : P.Face → I)

include hw ht in
/-- The protected exterior contributes at most the literal outside word length.
The cut term is the number of unordered genuine interior contacts, not darts. -/
theorem partition_face_bound {M : ℕ} {α β δ : ℝ} (ha : 0 ≤ α)
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d))
    (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) (hb : P.NoBigon)
    (hM : ∀ i, 8 * Fintype.card {F : InteriorFace n w d ell hell word c hc f P // part F.val = i} ≤ M) :
    defectConstant α β δ * Fintype.card (InteriorFace n w d ell hell word c hc f P) ≤
      (ell : ℝ) + 2 * Fintype.card (RelativeCutContact P.pairing
        (Interior n w d ell hell word c hc f P ∘ P.faceClass) (part ∘ P.faceClass)) := by
  have hp := actual_partition_bound n w d ell hell word c hc f P part ha hgood hs hm hred hrad hb hM
  have he : (Fintype.card (OutsideContact P.pairing
      (Interior n w d ell hell word c hc f P ∘ P.faceClass)) : ℝ) ≤ ell := by
    exact_mod_cast outside_contacts_le n w d ell hell word c hc f P xs hw ht
  linarith

include hx hw ht in
/-- Actual relator filling with its exact fragment-cut cost. This is valid for
every small partition, without assuming that a low-cut separator exists. -/
theorem partition_filling_bound {M : ℕ} {α β δ : ℝ} (ha : 0 ≤ α)
    (hk : 0 ≤ defectConstant α β δ)
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d))
    (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) (hb : P.NoBigon)
    (hM : ∀ i, 8 * Fintype.card {F : InteriorFace n w d ell hell word c hc f P // part F.val = i} ≤ M) :
    ∃ a, Homotopy (SimpleWordRelator n w d) (List.ofFn word) [] a ∧
      defectConstant α β δ * a ≤ 30 * ((ell : ℝ) +
        2 * Fintype.card (RelativeCutContact P.pairing
          (Interior n w d ell hell word c hc f P ∘ P.faceClass) (part ∘ P.faceClass))) := by
  obtain ⟨a,hfill,ha'⟩ := normal_disk_area n w d ell hell (letterDart n w ∘ word)
    (letterWordClosed n w ell word) c hc f P hm hs hb xs hx hw ht
  have he : (List.ofFn (letterDart n w ∘ word)).flatMap (collapse n w) = List.ofFn word := by
    rw [← List.map_ofFn]
    exact collapse_letter_word n w (List.ofFn word)
  rw [he] at hfill
  refine ⟨a,hfill,?_⟩
  rw [← interior_card n w d ell hell word c hc f P xs hx hw ht] at ha'
  have haR : (a : ℝ) ≤ 30 * Fintype.card (InteriorFace n w d ell hell word c hc f P) := by
    exact_mod_cast ha'
  have hp := partition_face_bound n w d ell hell word c hc f P xs hw ht part ha hgood hs hm hred hrad hb hM
  calc
    defectConstant α β δ * a ≤ defectConstant α β δ *
      (30 * Fintype.card (InteriorFace n w d ell hell word c hc f P)) := mul_le_mul_of_nonneg_left haR hk
    _ = 30 * (defectConstant α β δ * Fintype.card (InteriorFace n w d ell hell word c hc f P)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
