import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightBins
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightLeaf
import OAI.NumberTheory.Ostmann.Construction.InitialCoordinatesTemplateIndex

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.InitialCoordinatesTemplate
open Arithmetic

variable {b s k : ℕ} {a : State} {outside : List ℕ}

def stateIndex (ha : Template.Matches (Template.initial (2*b) k) a.small) :
    SmallShape b k ≃ Fin a.small.length :=
  (smallEquiv b k).trans (finCongr (matches_initial_length ha).symm)

def outsideIndex (hout : outside.length = 2*s) :
    (Bool × Fin s) ≃ Fin outside.length := (halfEquiv s).trans (finCongr hout.symm)

@[simp] theorem stateIndex_val (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (q : SmallShape b k) : (stateIndex ha q).val = (smallEquiv b k q).val := rfl

@[simp] theorem outsideIndex_val (hout : outside.length = 2*s) (h : Bool) (i : Fin s) :
    (outsideIndex hout (h,i)).val = (if h then s else 0)+i.val := halfEquiv_val s h i

def coordinates (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (hout : outside.length = 2*s) (plus minus : ℝ)
    (y : Fin a.small.length → ℝ) (z : Fin outside.length → ℝ) : InitialCoordinates b s k where
  giant h := if h then minus else plus
  bulk h i := y (stateIndex ha (.inl (h,i)))
  spectator h i := z (outsideIndex hout (h,i))
  top h i := y (stateIndex ha (.inr (.inl (h,i))))
  compensation h j i := y (stateIndex ha (.inr (.inr (j,(h,i)))))

theorem coordinates_positive
    (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (hout : outside.length = 2*s) (plus minus : ℝ)
    (y : Fin a.small.length → ℝ) (z : Fin outside.length → ℝ)
    (hp : 0 < plus) (hm : 0 < minus) (hy : ∀i,0 < y i) (hz : ∀i,0 < z i) :
    (coordinates ha hout plus minus y z).Positive := by
  refine ⟨?_,fun h i => hy _,fun h i => hz _,fun h i => hy _,fun h j i => hy _⟩
  intro h
  cases h <;> assumption

theorem small_product (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (y : Fin a.small.length → ℝ) :
    (∏h,∏i,y (stateIndex ha (.inl (h,i)))) *
      (∏h,∏i,y (stateIndex ha (.inr (.inl (h,i))))) *
      (∏h,∏j,∏i,y (stateIndex ha (.inr (.inr (j,(h,i)))))) = ∏i,y i := by
  have he := (stateIndex ha).prod_comp y
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type] at he
  rw [Finset.prod_comm (f := fun j h => ∏i,y (stateIndex ha (.inr (.inr (j,(h,i))))))] at he
  simpa only [mul_assoc] using he

theorem spectator_product (hout : outside.length = 2*s) (z : Fin outside.length → ℝ) :
    (∏h,∏i,z (outsideIndex hout (h,i))) = ∏i,z i := by
  simpa only [Fintype.prod_prod_type] using (outsideIndex hout).prod_comp z

theorem coordinates_product
    (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (hout : outside.length = 2*s) (plus minus : ℝ)
    (y : Fin a.small.length → ℝ) (z : Fin outside.length → ℝ) :
    (coordinates ha hout plus minus y z).product =
      (∏i,z i) * (plus * (minus * ∏i,y i)) := by
  unfold InitialCoordinates.product coordinates
  simp only [Fintype.prod_bool, Bool.false_eq_true, ↓reduceIte]
  have hs := spectator_product hout z
  have hy := small_product ha y
  simp only [Fintype.prod_bool] at hs hy
  rw [←hs, ←hy]
  ring

theorem bulk_index_membership
    (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (h : Bool) (q : SmallShape b k) :
    sourceBulkHalf b h (a.small.get (stateIndex ha q)) ↔
      ∃i : Fin b, q = .inl (h,i) := by
  obtain ⟨ho,hr⟩ := matches_initial_metadata ha (stateIndex ha q)
  unfold sourceBulkHalf
  rw [ho,hr]
  rcases q with ⟨g,i⟩ | (⟨g,i⟩ | ⟨j,g,i⟩)
  · have hv := stateIndex_val ha (.inl (g,i))
    rw [smallEquiv_bulk_val] at hv
    rw [hv]
    have hi := i.isLt
    cases h <;> cases g <;> simp <;> omega
  · have hn : ¬(stateIndex ha (.inr (.inl (g,i)))).val < 2*b := by
      rw [stateIndex_val, smallEquiv_top_val]
      cases g <;> simp
      omega
    simp only [hn, false_and, Sum.inr_ne_inl, exists_false]
  · have hn : ¬(stateIndex ha (.inr (.inr (j,(g,i))))).val < 2*b := by
      rw [stateIndex_val, smallEquiv_compensation_val]
      cases g <;> simp <;> omega
    simp only [hn, false_and, Sum.inr_ne_inl, exists_false]

theorem spectator_index_membership (hout : outside.length = 2*s)
    (h g : Bool) (i : Fin s) :
    sourceSpectatorHalf s h (outsideIndex hout (g,i)).val ↔ g=h := by
  unfold sourceSpectatorHalf
  rw [outsideIndex_val]
  have hi := i.isLt
  cases h <;> cases g <;> simp
  omega

theorem bulk_log_sum (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (h : Bool) (y : Fin a.small.length → ℝ) :
    (∑i,if sourceBulkHalf b h (a.small.get i) then Real.log (y i) else 0) =
      ∑i,Real.log (y (stateIndex ha (.inl (h,i)))) := by
  rw [←(stateIndex ha).sum_comp (fun i =>
    if sourceBulkHalf b h (a.small.get i) then Real.log (y i) else 0)]
  simp only [bulk_index_membership, Fintype.sum_sum_type, Fintype.sum_prod_type]
  cases h <;> simp

theorem spectator_log_sum (hout : outside.length = 2*s)
    (h : Bool) (z : Fin outside.length → ℝ) :
    (∑i,if sourceSpectatorHalf s h i.val then Real.log (z i) else 0) =
      ∑i,Real.log (z (outsideIndex hout (h,i))) := by
  rw [←(outsideIndex hout).sum_comp (fun i =>
    if sourceSpectatorHalf s h i.val then Real.log (z i) else 0)]
  simp only [Fintype.sum_prod_type, spectator_index_membership]
  cases h <;> simp

theorem coordinates_bins
    (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (hout : outside.length = 2*s) (plus minus tb td : ℝ)
    (y : Fin a.small.length → ℝ) (z : Fin outside.length → ℝ) :
    realLeafBins (coordinates ha hout plus minus y z) tb td =
      realStateBins b s tb td a outside y z := by
  unfold realLeafBins realStateBins
  simp only [bulk_log_sum ha, spectator_log_sum hout]
  rfl

end Ostmann.Construction.InitialCoordinatesTemplate

end

end OAI
