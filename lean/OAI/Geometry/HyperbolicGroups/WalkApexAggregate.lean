import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkTurnTransport
import OAI.Geometry.HyperbolicGroups.WalkRadialBoundary

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

/-- The summed apex estimate is now a theorem about the actual selected
mixed-picture faces. All nominal slots, turns, partial links and radial
boundary sides are extracted from the picture itself. -/
theorem actual_nominal_apex (hb : P.NoBigon) :
    3 * (Fintype.card (SelectedTopFace n w d c hc f P select) : ℝ) +
      2 * ((∑ b : Fan n w, ((indexedFanData n w d c hc f P select b hs hm hred hrad).weight : ℝ)) -
        7 * Fintype.card (SelectedTopFace n w d c hc f P select)) ≤
    ((∑ b : Fan n w, ((indexedFanData n w d c hc f P select b hs hm hred hrad).triangles : ℝ)) +
      ∑ b : Fan n w, ((indexedFanData n w d c hc f P select b hs hm hred hrad).payments : ℝ))/2 +
      2 * ∑ b : Fan n w, ((indexedFanData n w d c hc f P select b hs hm hred hrad).partialCount : ℝ) := by
  have ha := Finset.sum_le_sum (s := Finset.univ)
    (fun b _ => (indexedFanData n w d c hc f P select b hs hm hred hrad).apex_bound)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_div,← Finset.mul_sum] at ha
  have ht : 3 * (Fintype.card (SelectedTopFace n w d c hc f P select) : ℝ) ≤
      ∑ b : Fan n w, ((indexedFanData n w d c hc f P select b hs hm hred hrad).turns : ℝ) := by
    exact_mod_cast actual_turns_ge n w d c hc f P select hs hm hred hrad hb
  have hslot : (∑ b : Fan n w, (Fintype.card (SelectedTop n w d c hc f P select b) : ℝ)) =
      7 * Fintype.card (SelectedTopFace n w d c hc f P select) := by
    exact_mod_cast fragment_slots_eq n w d c hc f P select
  rw [hslot] at ha
  linarith

lemma actual_triangles_le :
    (∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).triangles) ≤
      5 * ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).weight := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun b _ => (indexedFanData n w d c hc f P select b hs hm hred hrad).triangles_le)
  simpa only [← Finset.mul_sum] using h

lemma actual_partial_le :
    2 * (∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).partialCount) ≤
      Fintype.card (RadialBoundarySide n w d c hc f P select) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun b _ => (indexedFanData n w d c hc f P select b hs hm hred hrad).partial_le_boundary)
  have h' : 2 * (∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).partialCount) ≤
      ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).boundary := by
    simpa only [← Finset.mul_sum] using h
  exact h'.trans (actual_radial_sides n w d c hc f P select hs hm hred hrad)

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
