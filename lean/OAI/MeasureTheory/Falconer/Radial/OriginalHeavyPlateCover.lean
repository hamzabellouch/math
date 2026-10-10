import OAI.MeasureTheory.Falconer.Radial.BoundedHeavyPlateCover
import OAI.MeasureTheory.Falconer.Measures.MeanProbability

namespace OAI

/-! # The heavy-plate cover for the sum of the two original probability laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem original_heavy_plate_cover (hpublished : PublishedHeavyHyperplanes)
    {d : ℕ} (hd : 3 ≤ d) (μ ν : ProbabilityMeasure (Space d)) {M s C : ℝ}
    (hM : 0 ≤ M) (hs : 1/2 < s-((d-2:ℕ):ℝ)) (hs' : s-((d-2:ℕ):ℝ) < 1) (hC : 0 ≤ C)
    (hμbounded : ∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ x ∂(ν : Measure (Space d)), ‖x‖ ≤ M)
    (hμfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hνfrost : FrostmanBallBound (ν : Measure (Space d)) s C) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ S : Finset (Space d × ℝ), (∀ p ∈ S, ‖p.1‖ = 1) ∧
        (S.card:ℝ) ≤ K*δ^(-heavyPlateExponent (s-((d-2:ℕ):ℝ))) ∧
        ∀ w : Space d, ‖w‖ = 1 → ∀ t : ℝ,
          ENNReal.ofReal (2*δ^(heavyPlateExponent (s-((d-2:ℕ):ℝ)))) ≤
            ((μ : Measure (Space d))+(ν : Measure (Space d))) {x | |inner ℝ w x-t| ≤ δ} →
          ∃ p ∈ S, ∀ x : Space d, ‖x‖ ≤ M → |inner ℝ w x-t| ≤ δ →
            |inner ℝ p.1 x-p.2| ≤ K*δ^(1/4:ℝ) := by
  obtain ⟨K,hK,hcover⟩ := bounded_heavy_plate_cover hpublished hd (meanProbability μ ν)
    hM hs hs' hC (meanProbability_ae μ ν _ hμbounded hνbounded)
    (meanProbability_frostman μ ν hμfrost hνfrost)
  refine ⟨K,hK,?_⟩
  intro δ hδ hδ1
  obtain ⟨S,hunit,hcard,hcoverS⟩ := hcover δ hδ hδ1
  refine ⟨S,hunit,hcard,?_⟩
  intro w hw t hheavy
  apply hcoverS w hw t
  apply meanProbability_heavy μ ν _ (δ^(heavyPlateExponent (s-((d-2:ℕ):ℝ))))
  simpa only [Measure.add_apply] using hheavy

end Falconer

end OAI
