import OAI.Geometry.RCD.Transport.LocalMidpointDensityComparison

namespace OAI

/-! # Almost-everywhere constant density on a midpoint-contraction neighborhood -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem local_midpoint_density_constant {n : ℕ} (hn : 0 < n)
    (μ : FiniteMeasure (Euclidean n)) (hμ : (μ : Measure (Euclidean n)) ≪ volume)
    (z : Euclidean n) {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ u ∈ ball z δ, ∀ v ∈ ball z δ, ∀ r : ℝ, 0 < r → r ≤ δ →
      (1/2:ℝ)^n*(μ : Measure (Euclidean n)).real (ball v r) ≤
        (μ : Measure (Euclidean n)).real (closedBall ((1/2:ℝ) • (u+v)) (r/2))) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᵐ x ∂volume.restrict (ball z (δ/4)),
      ((μ : Measure (Euclidean n)).rnDeriv volume x).toReal=c := by
  have hgood := euclidean_energy_density_limit μ
  have hex : ∃ x ∈ ball z (δ/4),
      Tendsto (fun r => (μ : Measure (Euclidean n)).real (closedBall x r)/
        volume.real (closedBall x r)) (𝓝[>] 0)
          (𝓝 (((μ : Measure (Euclidean n)).rnDeriv volume x).toReal)) := by
    by_contra hnot
    have hnull : ∀ᵐ x ∂(volume : Measure (Euclidean n)), x ∉ ball z (δ/4) := by
      filter_upwards [hgood] with x hx hball
      exact hnot ⟨x,hball,hx⟩
    have he : volume (ball z (δ/4))=0 := by
      simpa only [not_not,Set.ofPred_mem_eq] using ae_iff.mp hnull
    exact (measure_ball_pos volume z (by positivity)).ne' he
  obtain ⟨x,hx,hlimx⟩ := hex
  refine ⟨((μ : Measure (Euclidean n)).rnDeriv volume x).toReal,ENNReal.toReal_nonneg,?_⟩
  filter_upwards [ae_restrict_of_ae hgood,ae_restrict_mem measurableSet_ball] with y hy hyball
  exact local_midpoint_density_eq hn μ hμ z hδ hc hyball hx hy hlimx

end RegularPointCoordinates

end

end OAI
