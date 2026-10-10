import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkApexAggregate
import OAI.Geometry.HyperbolicGroups.ActualLayers
import OAI.Geometry.HyperbolicGroups.ActualRawAccount
import OAI.Geometry.HyperbolicGroups.Fragment

namespace OAI

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction
open IncidenceTemplate.Occurrences.Shape

lemma fragment_numeric_bound {α β δ : ℝ} (ha : 0 ≤ α)
    (T Q E V W S J I Br Bd : ℕ)
    (hI : (I : ℝ) ≤ ((3-β)-7*(2-α))*T + (2-α)*W + (2-δ)*E + (3-δ)*V)
    (hA : 3*(T : ℝ) + 2*((W : ℝ)-7*T) ≤ ((Q : ℝ)+S)/2 + 2*J)
    (hQ : Q ≤ 5*W) (hJ : 2*J ≤ Bd)
    (hR : S+Q+4*E+6*V ≤ Br+2*I) :
    defectConstant α β δ * (T+Q+E+V : ℕ) ≤ (Br+Bd : ℕ) := by
  have h1 : defectConstant α β δ ≤ β-7*α := min_le_left _ _
  have h2 : defectConstant α β δ ≤ α/5 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : defectConstant α β δ ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  have hQ' : (Q : ℝ) ≤ 5*W := by exact_mod_cast hQ
  have hQa : α/5*(Q : ℝ) ≤ α*W := by nlinarith
  have ht1 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) T)
  have ht2 := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg (α := ℝ) Q)
  have ht3 := mul_le_mul_of_nonneg_right h3 (show (0:ℝ) ≤ (E:ℝ)+V by positivity)
  have hJ' : 2*(J : ℝ) ≤ Bd := by exact_mod_cast hJ
  have hR' : (S : ℝ)+Q+4*E+6*V ≤ (Br : ℝ)+2*I := by exact_mod_cast hR
  have hBr : (0 : ℝ) ≤ Br := Nat.cast_nonneg _
  push_cast
  nlinarith

namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

def actualFanWeight := ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).weight
def actualPayments := ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).payments
def actualPartialCount := ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).partialCount
def actualBoundary := Fintype.card (ActualRawBoundary n w d c hc f P select) +
  Fintype.card (RadialBoundarySide n w d c hc f P select)

lemma actual_contacts_le {M : ℕ} {α β δ : ℝ}
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d)) (hb : P.NoBigon)
    (hM : 8 * actualArea n w d c hc f P select ≤ M) :
    (Fintype.card (ActualContact n w d c hc f P select) : ℝ) ≤
      ((3-β)-7*(2-α)) * actualTopCount n w d c hc f P select +
      (2-α) * actualFanWeight n w d c hc f P select hs hm hred hrad +
      (2-δ) * actualSquareCount n w d c hc f P select +
      (3-δ) * actualSixCount n w d c hc f P select := by
  have hl := actual_layer_bounds n w d c hc f P select hs hm hred hrad hb hM
  have hh := actual_contact_bound n w d c hc f P select hs hm hred hrad hgood hb
    (fun j => (hl j).1) (fun j => (hl j).2.1) (fun j => (hl j).2.2.1) (fun j => (hl j).2.2.2)
  dsimp only at hh
  have ht : (∑ a, ((actualWeights n w d c hc f P select hs hm hred hrad).top a : ℝ)) =
      actualTopCount n w d c hc f P select := by
    exact_mod_cast actual_weights_top n w d c hc f P select hs hm hred hrad
  have hf : (∑ b, ((actualWeights n w d c hc f P select hs hm hred hrad).fan b : ℝ)) =
      actualFanWeight n w d c hc f P select hs hm hred hrad := by
    exact_mod_cast actual_weights_fan n w d c hc f P select hs hm hred hrad
  have hq : (∑ q, ((actualWeights n w d c hc f P select hs hm hred hrad).square q : ℝ)) =
      actualSquareCount n w d c hc f P select := by
    exact_mod_cast actual_weights_square n w d c hc f P select hs hm hred hrad
  have hv : (∑ q, ((actualWeights n w d c hc f P select hs hm hred hrad).six q : ℝ)) =
      actualSixCount n w d c hc f P select := by
    exact_mod_cast actual_weights_six n w d c hc f P select hs hm hred hrad
  rwa [ht,hf,hq,hv] at hh

include hs hm hred hrad in
/-- The full fragment estimate for the literal normalized mixed
picture, for ANY selected faces. All counts, weights, normal fan links,
indexed coincidences and size bounds are produced, not assumed. -/
theorem actual_fragment_bound {M : ℕ} {α β δ : ℝ} (ha : 0 ≤ α)
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d)) (hb : P.NoBigon)
    (hM : 8 * actualArea n w d c hc f P select ≤ M) :
    defectConstant α β δ * actualArea n w d c hc f P select ≤
      actualBoundary n w d c hc f P select := by
  have hI := actual_contacts_le n w d c hc f P select hs hm hred hrad hgood hb hM
  have hA := actual_nominal_apex n w d c hc f P select hs hm hred hrad hb
  have hQ := actual_triangles_le n w d c hc f P select hs hm hred hrad
  have hJ := actual_partial_le n w d c hc f P select hs hm hred hrad
  have hR := actual_raw_lower n w d c hc f P select hs hm hred hrad hb
  have hC := actual_boundary_contacts_eq n w d c hc f P select
  rw [← hC] at hR
  have hT := selectedTriangles_eq n w d c hc f P select hs hm hred hrad hb
  have hu : @Finset.univ (Fan n w) (Subtype.fintype _) =
      @Finset.univ (Fan n w) inferInstance := by ext x; simp
  try simp only [hu] at hA hQ hJ hT
  have hA' : 3*(actualTopCount n w d c hc f P select : ℝ) +
      2*((actualFanWeight n w d c hc f P select hs hm hred hrad : ℝ)-7*actualTopCount n w d c hc f P select) ≤
      ((actualTriangleCount n w d c hc f P select : ℝ)+actualPayments n w d c hc f P select hs hm hred hrad)/2 +
      2*actualPartialCount n w d c hc f P select hs hm hred hrad := by
    have ht' : (∑ b : Fan n w, ((indexedFanData n w d c hc f P select b hs hm hred hrad).triangles : ℝ)) =
        actualTriangleCount n w d c hc f P select := by
      have ht0 : (∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).triangles) =
          actualTriangleCount n w d c hc f P select := by
        simpa only [actualTriangleCount,← Nat.card_eq_fintype_card] using hT.symm
      exact_mod_cast ht0
    simpa only [actualTopCount,actualFanWeight,actualPayments,actualPartialCount,Nat.cast_sum,ht',← Nat.card_eq_fintype_card] using hA
  have hQ' : actualTriangleCount n w d c hc f P select ≤
      5 * actualFanWeight n w d c hc f P select hs hm hred hrad := by
    change Fintype.card (SelectedTriangleFace n w d c hc f P select) ≤ _
    rw [hT]
    simpa only [actualFanWeight] using hQ
  change 2 * actualPartialCount n w d c hc f P select hs hm hred hrad ≤ _ at hJ
  rw [actual_area_eq n w d c hc f P select]
  exact fragment_numeric_bound ha _ _ _ _ _ _ _ _ _ _ hI hA' hQ' hJ hR

end ConeSkeleton
end HyperbolicObstruction
end

end OAI
