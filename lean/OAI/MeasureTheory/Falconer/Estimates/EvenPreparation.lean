import OAI.MeasureTheory.Falconer.Angular.EvenStartingCaps

namespace OAI

/-! # Even-dimensional starting pairs in the original compact set

This is the even-dimensional branch of `prep:starting-pairs`, not the
all-dimensional distance theorem. The cap and exceptional-set conclusions
refer to the original marginal laws in `Space (2*h)`.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem even_starting_pairs_of_published
    (hF : PublishedFrostmanAboveHalf) (hR : PublishedRadialMoment)
    {h : ℕ} (hh : 1 ≤ h) (E : Set (Space (2*h))) (hE : IsCompact E)
    (hDim : ((2*h:ℕ) : ℝ≥0∞)/2 < dimH E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ζ : ProbabilityMeasure (Space (2*h))) (δ : ℝ), 0 < δ ∧ δ < 1 ∧
      ∃ p : ProjectedStartingPair ζ (h+1) ((h:ℝ)+δ) ε,
        (p.left : Measure (Space (2*h))).support ⊆ E ∧
        (p.right : Measure (Space (2*h))).support ⊆ E ∧
        CapAvailable p.left p.right (fun _ => p.relation) (h:ℝ) := by
  have hd : 2 ≤ 2*h := by omega
  obtain ⟨s,hs,_,ζ,hζ,C,_,hfrost⟩ := hF (2*h) hd E hE hDim
  have hhs : (h:ℝ) < s := by
    push_cast at hs
    linarith only [hs]
  obtain ⟨δ,hδ,hδ1,p,hcap⟩ := exists_even_starting_caps hR hh ζ hhs hfrost hε
  have hsupp : (ζ : Measure (Space (2*h))).support ⊆ E :=
    Measure.support_subset_of_isClosed hE.isClosed hζ
  exact ⟨ζ,δ,hδ,hδ1,p,p.left_ac.support_mono.trans hsupp,
    p.right_ac.support_mono.trans hsupp,hcap⟩

end Falconer

end OAI
