import Mathlib
import OAI.Geometry.HyperbolicGroups.ActualLayers
import OAI.Geometry.HyperbolicGroups.RelativeFaceCounts

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_top_layer (j : ℕ) :
    Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).TopAt j) ≤
      actualTopCount n w d ell hell word c hc f P select := by
  rw [← actual_weights_top n w d ell hell word c hc f P select hs hm hred hrad]
  exact card_layer_le_support _ _ j (fun _ h => h)
lemma actual_square_layer (j : ℕ) :
    Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).SquareAt j) ≤
      actualSquareCount n w d ell hell word c hc f P select := by
  rw [← actual_weights_square n w d ell hell word c hc f P select hs hm hred hrad]
  exact card_layer_le_support _ _ j (fun _ h => h)
lemma actual_six_layer (j : ℕ) :
    Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).SixAt j) ≤
      actualSixCount n w d ell hell word c hc f P select := by
  rw [← actual_weights_six n w d ell hell word c hc f P select hs hm hred hrad]
  exact card_layer_le_support _ _ j (fun _ h => h)

lemma actual_fan_layer (hb : P.NoBigon) (j : ℕ) :
    Fintype.card ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).FanAt j) ≤
      7 * actualTopCount n w d ell hell word c hc f P select + actualTriangleCount n w d ell hell word c hc f P select := by
  let D := fun b => indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad
  have hh := card_layer_le_support (fun b => (actualWeights n w d ell hell word c hc f P select hs hm hred hrad).fan b)
    (fun b => Fintype.card (SelectedTop n w d ell hell word c hc f P select ((enumFan n w).symm b)) +
      (D ((enumFan n w).symm b)).triangles) j
        (fun fan hactive => (D ((enumFan n w).symm fan)).activation_bound hactive)
  have he := Equiv.sum_comp (enumFan n w).symm (fun b =>
    Fintype.card (SelectedTop n w d ell hell word c hc f P select b) + (D b).triangles)
  rw [he,Finset.sum_add_distrib] at hh
  have hslot : (∑ b : Fan n w, Fintype.card (SelectedTop n w d ell hell word c hc f P select b)) =
      7 * actualTopCount n w d ell hell word c hc f P select := by
    have h0 := fragment_slots_eq n w d ell hell word c hc f P select
    simp only [actualTopCount,← Nat.card_eq_fintype_card] at h0 ⊢
    convert h0 using 1
    congr 1
    ext face
    simp
  rw [hslot] at hh
  have ht : actualTriangleCount n w d ell hell word c hc f P select = ∑ b, (D b).triangles := by
    have h0 := selectedTriangles_eq n w d ell hell word c hc f P select hs hm hred hrad hb
    simp only [actualTriangleCount,← Nat.card_eq_fintype_card] at h0 ⊢
    convert h0 using 1
    congr 1
    ext face
    simp
  rw [← ht] at hh
  exact hh

lemma actual_layer_bounds (hsel : InteriorSelection n w d ell hell word c hc f P select) {M : ℕ} (hb : P.NoBigon) (hM : 8 * actualArea n w d ell hell word c hc f P select ≤ M) (j : ℕ) :
    let W := actualWeights n w d ell hell word c hc f P select hs hm hred hrad
    Fintype.card (W.TopAt j) ≤ M ∧ Fintype.card (W.FanAt j) ≤ M ∧
      Fintype.card (W.SquareAt j) ≤ M ∧ Fintype.card (W.SixAt j) ≤ M := by
  have ht := actual_top_layer n w d ell hell word c hc f P select hs hm hred hrad j
  have hf := actual_fan_layer n w d ell hell word c hc f P select hs hm hred hrad hb j
  have hq := actual_square_layer n w d ell hell word c hc f P select hs hm hred hrad j
  have hv := actual_six_layer n w d ell hell word c hc f P select hs hm hred hrad j
  rw [actual_area_eq n w d ell hell word c hc f P select hsel] at hM
  dsimp only
  omega

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
