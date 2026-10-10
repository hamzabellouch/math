import OAI.MeasureTheory.Falconer.Angular.OddOriginalCaps
import OAI.MeasureTheory.Falconer.Estimates.OddProjectedPieces
import OAI.MeasureTheory.Falconer.Angular.EvenStartingCaps

namespace OAI

/-! # Starting-pair cap preparation in the noncharging odd-dimensional branch -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem odd_noncharging_starting_pairs
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} (E : Set (Space (2*h+3))) (hE : IsCompact E)
    (μ : ProbabilityMeasure (Space (2*h+3)))
    (hμE : (μ : Measure (Space (2*h+3))) Eᶜ = 0)
    {s C ε : ℝ} (hs : (h:ℝ)+3/2 < s)
    (hfrost : FrostmanBallBound (μ : Measure (Space (2*h+3))) s C)
    (hnull : ∀ x : Space (2*h+3), ∀ V : Submodule ℝ (Space (2*h+3)),
      Module.finrank ℝ V ≤ h+2 → (μ : Measure (Space (2*h+3))) {y | y-x ∈ V} = 0)
    (hε : 0 < ε) {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ α : ℝ, (h:ℝ)+3/2 < α ∧ α < (h:ℝ)+2 ∧
      ∃ (ζ : ProbabilityMeasure (Space (2*h+3)))
        (p : ProjectedStartingPair ζ (h+3) α ε),
        (p.left : Measure (Space (2*h+3))).support ⊆ E ∧
        (p.right : Measure (Space (2*h+3))).support ⊆ E ∧
        ∃ Γ : ℕ → Set (Space (2*h+3) × Space (2*h+3)),
          (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
          0 < ((p.left : Measure (Space (2*h+3))).prod
            (p.right : Measure (Space (2*h+3)))) (⋂ N, Γ N) ∧
          (∀ N, Γ N ⊆ p.relation) ∧
          CapAvailable p.left p.right Γ ((h:ℝ)+3/2) := by
  have hs' : ((h+2:ℕ):ℝ)-1/2 < s := by push_cast; linarith
  obtain ⟨δ,hδ,hδ1,ζ,hK,hdom,f,⟨p⟩⟩ :=
    choose_odd_projected_pieces (by omega : 2 ≤ h+2) μ hs' hfrost hnull hε
  have hα : (h:ℝ)+3/2 < ((h+2:ℕ):ℝ)-1/2+δ := by push_cast; linarith
  have hα' : ((h+2:ℕ):ℝ)-1/2+δ < (h:ℝ)+2 := by push_cast; linarith
  obtain ⟨Γ,hΓ,hanti,hpos,hΓsub,hcap⟩ := p.odd_original_caps hR hH hF hLW hα hα' hω hω1
  have hsupp : (μ : Measure (Space (2*h+3))).support ⊆ E :=
    Measure.support_subset_of_isClosed hE.isClosed hμE
  exact ⟨_,hα,hα',ζ,p.firstPair,(p.left_ac.trans hdom).support_mono.trans hsupp,
    (p.right_ac.trans hdom).support_mono.trans hsupp,Γ,hΓ,hanti,hpos,hΓsub,hcap⟩

end Falconer

end OAI
