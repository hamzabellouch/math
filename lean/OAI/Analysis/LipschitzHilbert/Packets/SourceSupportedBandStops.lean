import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedTopEnvelope

namespace OAI

/-! Clipping a band's stopping level changes no packet when that band
has no items. This permits itemwise shortness in every later motion bound. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {ι : Type*} {N : ℕ} {κ : Type} {Label : Fin N → Type}
  {Item : ∀ j, Label j → Type} [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem sourceBandAmplitude_clip_stop (g : AngularGrid)
    (tops : Finset ι) (slope precision : ι → ℝ) (cut : ℝ)
    (weight : ι → (ℝ×ℝ) → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (P : ι → SourceLabeledLattice N κ Label Item)
    (coeff : ∀ t j (l : (P t).labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (rawStop : ι → Fin N → ℕ) (M : ι → ℕ)
    (hstop : ∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l), rawStop t j ≤ M t)
    (x y : ι → ℝ) (phase : ℕ → ℂ) (a : ℝ) (z : ℝ×ℝ) (level : ℕ) (cell : ℤ) :
    g.sourcePacketAmplitude tops slope precision cut weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => rawStop p.1 p.2)
      (fun p => (P p.1).rawBand (coeff p.1) i p.2 (x p.1) (y p.1)) phase a z level cell =
    g.sourcePacketAmplitude tops slope precision cut weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst
      (fun p => min (rawStop p.1 p.2) (M p.1))
      (fun p => (P p.1).rawBand (coeff p.1) i p.2 (x p.1) (y p.1)) phase a z level cell := by
  apply g.sourcePacketAmplitude_stop_congr_of_zero
  intro p hp
  by_cases hs : rawStop p.1 p.2 ≤ M p.1
  · exact Or.inl (min_eq_left hs).symm
  · right
    apply (P p.1).rawBand_eq_zero_of_no_item
    intro l u
    exact hs (hstop p.1 (Finset.mem_product.mp hp).1 p.2 l u)

/-- The actual eligibility stop is bounded whenever an item exists. -/
theorem source_length_stop_le_of_item (g : AngularGrid)
    (tops : Finset ι) (T : ι → SlopeBox) (P : ι → SourceLabeledLattice N κ Label Item)
    (w cut : ℝ) (hw : 0 < w) (M : ι → ℕ)
    (hzero : ∀ t ∈ tops, ∀ j, g.eligible cut (w/(P t).length j) 0)
    (hshort : ∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
      (P t).length j ≤ (T t).length)
    (hmax : ∀ t ∈ tops, ∀ k, g.eligible cut (w/(T t).length) k → k ≤ M t)
    (t : ι) (ht : t ∈ tops) (j : Fin N) (l : (P t).labels j) (u : Item j l) :
    g.lastEligible cut (w/(P t).length j) (div_pos hw ((P t).length_pos j)) ≤ M t := by
  apply hmax t ht
  have hj := g.eligible_lastEligible cut (w/(P t).length j)
    (div_pos hw ((P t).length_pos j)) (hzero t ht j)
  exact (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left hw.le ((P t).length_pos j) (hshort t ht j l u))
    (by positivity)).trans hj

end LipschitzHilbert.AngularGrid

end

end OAI
