import Mathlib
import OAI.Geometry.HyperbolicGroups.ActualRawAccount
import OAI.Geometry.HyperbolicGroups.RelativeFaceCounts
import OAI.Geometry.HyperbolicGroups.RelativeRawCount

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

lemma decorationSideIndex_card :
    Fintype.card (DecorationSideIndex n w d ell hell word c hc f P select) =
      4 * actualSquareCount n w d ell hell word c hc f P select + 6 * actualSixCount n w d ell hell word c hc f P select := by
  rw [Fintype.card_sigma,Fintype.sum_sum_type]
  simp only [Fintype.card_prod,Fintype.card_fin]
  change (∑ q : Square n w, Fintype.card (KindFace n w d ell hell word c hc f P select (.inr (.inr (.inl q)))) * 4) +
    (∑ q : Six n d, Fintype.card (KindFace n w d ell hell word c hc f P select (.inr (.inr (.inr q)))) * 6) = _
  rw [← Finset.sum_mul,← Finset.sum_mul]
  change actualSquareCount n w d ell hell word c hc f P select * 4 + actualSixCount n w d ell hell word c hc f P select * 6 = _
  omega

lemma actual_raw_lower (hb : P.NoBigon) :
    (∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).payments) +
      actualTriangleCount n w d ell hell word c hc f P select + 4 * actualSquareCount n w d ell hell word c hc f P select +
      6 * actualSixCount n w d ell hell word c hc f P select ≤ Fintype.card (ActualRawSide n w d ell hell word c hc f P select) := by
  have hh := actual_raw_account_le n w d ell hell word c hc f P select hs hm hred hrad hb
  change Fintype.card (AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad ⊕
    (AllTriangleIndex n w d ell hell word c hc f P select hs hm hred hrad ⊕ DecorationSideIndex n w d ell hell word c hc f P select)) ≤ _ at hh
  rw [Fintype.card_sum,Fintype.card_sum] at hh
  have hp : Fintype.card (AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad) =
      ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).payments := by
    have h0 := allPaymentIndex_card n w d ell hell word c hc f P select hs hm hred hrad
    simp only [← Nat.card_eq_fintype_card] at h0 ⊢
    convert h0 using 1
    congr 1
    ext index
    simp
  have ht : Fintype.card (AllTriangleIndex n w d ell hell word c hc f P select hs hm hred hrad) =
      actualTriangleCount n w d ell hell word c hc f P select := by
    have h0 := (allTriangleIndex_card n w d ell hell word c hc f P select hs hm hred hrad).trans
      (selectedTriangles_eq n w d ell hell word c hc f P select hs hm hred hrad hb).symm
    simpa only [actualTriangleCount,← Nat.card_eq_fintype_card] using h0
  rw [hp,ht,decorationSideIndex_card n w d ell hell word c hc f P select] at hh
  omega

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
