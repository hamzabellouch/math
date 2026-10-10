import Mathlib
import OAI.Geometry.HyperbolicGroups.ActualFragment
import OAI.Geometry.HyperbolicGroups.RelativeApexAggregate
import OAI.Geometry.HyperbolicGroups.RelativeLayers
import OAI.Geometry.HyperbolicGroups.RelativeRawAccount

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate.Occurrences.Shape
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
variable (hsel : InteriorSelection n w d ell hell word c hc f P select)
variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

def actualFanWeight := ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).weight
def actualPayments := ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).payments
def actualPartialCount := ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).partialCount
def actualBoundary := Fintype.card (ActualRawBoundary n w d ell hell word c hc f P select) +
  Fintype.card (RadialBoundarySide n w d ell hell word c hc f P select)

include hsel in
lemma actual_contacts_le {M : ℕ} {α β δ : ℝ}
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d)) (hb : P.NoBigon)
    (hM : 8 * actualArea n w d ell hell word c hc f P select ≤ M) :
    (Fintype.card (ActualContact n w d ell hell word c hc f P select) : ℝ) ≤
      ((3-β)-7*(2-α)) * actualTopCount n w d ell hell word c hc f P select +
      (2-α) * actualFanWeight n w d ell hell word c hc f P select hs hm hred hrad +
      (2-δ) * actualSquareCount n w d ell hell word c hc f P select +
      (3-δ) * actualSixCount n w d ell hell word c hc f P select := by
  have hl := actual_layer_bounds n w d ell hell word c hc f P select hs hm hred hrad hsel hb hM
  have hh := actual_contact_bound n w d ell hell word c hc f P select hsel hs hm hred hrad hgood hb
    (fun j => (hl j).1) (fun j => (hl j).2.1) (fun j => (hl j).2.2.1) (fun j => (hl j).2.2.2)
  dsimp only at hh
  have ht : (∑ a, ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).top a : ℝ)) =
      actualTopCount n w d ell hell word c hc f P select := by
    exact_mod_cast actual_weights_top n w d ell hell word c hc f P select hs hm hred hrad
  have hf : (∑ b, ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).fan b : ℝ)) =
      actualFanWeight n w d ell hell word c hc f P select hs hm hred hrad := by
    exact_mod_cast actual_weights_fan n w d ell hell word c hc f P select hs hm hred hrad
  have hq : (∑ q, ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).square q : ℝ)) =
      actualSquareCount n w d ell hell word c hc f P select := by
    exact_mod_cast actual_weights_square n w d ell hell word c hc f P select hs hm hred hrad
  have hv : (∑ q, ((actualWeights n w d ell hell word c hc f P select hs hm hred hrad).six q : ℝ)) =
      actualSixCount n w d ell hell word c hc f P select := by
    exact_mod_cast actual_weights_six n w d ell hell word c hc f P select hs hm hred hrad
  rwa [ht,hf,hq,hv] at hh

include hs hm hred hrad hsel in
/-- The full fragment estimate for the literal normalized mixed
picture, for any selected interior faces, with boundary contacts to the protected exterior counted. All counts, weights, normal fan links,
indexed coincidences and size bounds are produced, not assumed. -/
theorem actual_fragment_bound {M : ℕ} {α β δ : ℝ} (ha : 0 ≤ α)
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d)) (hb : P.NoBigon)
    (hM : 8 * actualArea n w d ell hell word c hc f P select ≤ M) :
    defectConstant α β δ * actualArea n w d ell hell word c hc f P select ≤
      actualBoundary n w d ell hell word c hc f P select := by
  have hI := actual_contacts_le n w d ell hell word c hc f P select hsel hs hm hred hrad hgood hb hM
  have hA := actual_nominal_apex n w d ell hell word c hc f P select hs hm hred hrad hb
  have hQ := actual_triangles_le n w d ell hell word c hc f P select hs hm hred hrad
  have hJ := actual_partial_le n w d ell hell word c hc f P select hs hm hred hrad
  have hR := actual_raw_lower n w d ell hell word c hc f P select hs hm hred hrad hb
  have hC := actual_boundary_contacts_eq n w d ell hell word c hc f P select
  rw [← hC] at hR
  have hT := selectedTriangles_eq n w d ell hell word c hc f P select hs hm hred hrad hb
  have hu : @Finset.univ (Fan n w) (Subtype.fintype _) =
      @Finset.univ (Fan n w) inferInstance := by ext x; simp
  try simp only [hu] at hA hQ hJ hT
  have hA' : 3*(actualTopCount n w d ell hell word c hc f P select : ℝ) +
      2*((actualFanWeight n w d ell hell word c hc f P select hs hm hred hrad : ℝ)-7*actualTopCount n w d ell hell word c hc f P select) ≤
      ((actualTriangleCount n w d ell hell word c hc f P select : ℝ)+actualPayments n w d ell hell word c hc f P select hs hm hred hrad)/2 +
      2*actualPartialCount n w d ell hell word c hc f P select hs hm hred hrad := by
    have ht' : (∑ b : Fan n w, ((indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).triangles : ℝ)) =
        actualTriangleCount n w d ell hell word c hc f P select := by
      have ht0 : (∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).triangles) =
          actualTriangleCount n w d ell hell word c hc f P select := by
        simpa only [actualTriangleCount,← Nat.card_eq_fintype_card] using hT.symm
      exact_mod_cast ht0
    simpa only [actualTopCount,actualFanWeight,actualPayments,actualPartialCount,Nat.cast_sum,ht',← Nat.card_eq_fintype_card] using hA
  have hQ' : actualTriangleCount n w d ell hell word c hc f P select ≤
      5 * actualFanWeight n w d ell hell word c hc f P select hs hm hred hrad := by
    change Fintype.card (SelectedTriangleFace n w d ell hell word c hc f P select) ≤ _
    rw [hT]
    simpa only [actualFanWeight] using hQ
  change 2 * actualPartialCount n w d ell hell word c hc f P select hs hm hred hrad ≤ _ at hJ
  rw [actual_area_eq n w d ell hell word c hc f P select hsel]
  exact fragment_numeric_bound ha _ _ _ _ _ _ _ _ _ _ hI hA' hQ' hJ hR

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
