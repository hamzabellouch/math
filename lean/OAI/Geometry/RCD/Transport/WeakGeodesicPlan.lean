import OAI.Geometry.RCD.Transport.GeodesicPlanTightness

namespace OAI

/-! # Geodesicity and endpoint laws of a weak limit -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem weak_limit_geodesic
    (πs : ℕ → ProbabilityMeasure C(Time,X)) (π : ProbabilityMeasure C(Time,X))
    (hlim : Tendsto πs atTop (𝓝 π))
    (hg : ∀ j, ∀ᵐ γ ∂(πs j : Measure C(Time,X)), IsGeodesic γ) :
    ∀ᵐ γ ∂(π : Measure C(Time,X)), IsGeodesic γ := by
  rw [ae_iff]
  change (π : Measure C(Time,X)) {γ | IsGeodesic γ}ᶜ=0
  apply le_antisymm ?_ (show (0 : ℝ≥0∞)≤_ from bot_le)
  have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
    (isClosed_geodesicSet (X:=X)).isOpen_compl
  have he : (fun j => (πs j : Measure C(Time,X)) {γ | IsGeodesic γ}ᶜ)=fun _ => 0 := by
    funext j
    exact (ae_iff.mp (hg j))
  simpa only [he,liminf_const] using h

theorem weak_limit_endpoint
    (πs : ℕ → ProbabilityMeasure C(Time,X)) (π : ProbabilityMeasure C(Time,X))
    (νs : ℕ → ProbabilityMeasure X) (ν : ProbabilityMeasure X) (t : Time)
    (hlim : Tendsto πs atTop (𝓝 π)) (hν : Tendsto νs atTop (𝓝 ν))
    (he : ∀ j, (πs j).map (fun γ => γ t)=νs j) :
    π.map (fun γ => γ t)=ν := by
  have hl := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim
    (continuous_eval_const t)
  have heq : (fun j => (πs j).map (fun γ => γ t))=νs := funext he
  rw [heq] at hl
  exact tendsto_nhds_unique hl hν

end RegularPointCoordinates

end

end OAI
