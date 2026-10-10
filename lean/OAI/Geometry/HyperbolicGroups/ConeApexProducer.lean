import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkFragment
import OAI.Geometry.HyperbolicGroups.FiniteFanData

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)

abbrev SelectedOccurrence := {a : Top n w // ∃ F : P.Face, select F = true ∧ P.faceKind F = .inl a}

noncomputable instance : Fintype (SelectedOccurrence n w d c hc f P select) := Fintype.ofFinite _

variable (b : Fan n w)

def selectedOccurrence' (F : SelectedTop n w d c hc f P select b) :
    SelectedOccurrence n w d c hc f P select :=
  ⟨selectedOccurrence n w d c hc f P select b F,F.val,F.property.1,
    selectedOccurrence_kind n w d c hc f P select b F⟩

/-- The actual selected fragment of an actual normalized genus-zero mapped
picture supplies EVERY field of the local fan-link data. No apex bound,
no triangle-link normality and no contact separation is assumed. -/
def indexedFanData (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) :
    FanLink.IndexedFanData (ApexInstance n w d c hc f P select b)
      (SelectedTop n w d c hc f P select b) (SelectedOccurrence n w d c hc f P select)
      (fun z => P.Link z.val) where
  next := fun z => P.linkNext z.val
  cyclic := fun z => P.link_cyclic z.val
  mark := fragmentMark n w d c hc f P select b
  line := fun _ x => dartPart n w (walkLabel n w d (P.index x.val))
  occurrence := selectedOccurrence' n w d c hc f P select b
  represented := fragment_represented n w d c hc f P select b
  card_le := fragment_card n w d c hc f P select b hrad
  no_fixed := fragment_no_fixed n w d c hc f P select b hm hred
  bipartite := fragment_bipartite n w d c hc f P select b hm
  no_backtrack := fragment_no_backtrack n w d c hc f P select b hm hred
  no_same_side := by
    intro z x F G hx hy h
    exact fragment_no_same_side n w d c hc f P select b hred z x F G hx hy (congrArg Subtype.val h)
  unique_turn := fragment_unique_turn n w d c hc f P select b hs

def actualFanData (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) :
    FanLink.FanData (Fintype.card (ApexInstance n w d c hc f P select b))
      (Fintype.card (SelectedTop n w d c hc f P select b))
      (Fintype.card (SelectedOccurrence n w d c hc f P select)) :=
  (indexedFanData n w d c hc f P select b hs hm hred hrad).toFin

/-- The one-fan nominal apex inequality for the actual link extraction
and every selection of faces in the picture. -/
theorem actual_apex_bound (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) :
    let L := actualFanData n w d c hc f P select b hs hm hred hrad
    (L.turns : ℝ) + 2 * ((L.weight : ℝ) - Fintype.card (SelectedTop n w d c hc f P select b)) ≤
      ((L.triangles : ℝ) + L.payments) / 2 + 2 * L.partialCount := by
  exact (actualFanData n w d c hc f P select b hs hm hred hrad).apex_bound

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
