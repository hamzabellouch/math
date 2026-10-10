import OAI.Geometry.RCD.Transport.BoundedPlanEntropyChord
import OAI.Geometry.RCD.Transport.BoltzmannSupportBounds

namespace OAI

/-! # Explicit entropy bounds for a compressed optimal plan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem bounded_plan_entropy_bounds (μ : Measure X) [SigmaFinite μ] [IsLocallyFiniteMeasure μ]
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ} (hC : 0 < C) (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • μ)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R) (t : Time) :
    -Real.log (μ.real (closedBall p (3*R))) ≤ boltzmannEntropy μ (π.map (fun γ => γ t)) ∧
      boltzmannEntropy μ (π.map (fun γ => γ t)) ≤ Real.log C ∧
      Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv μ x).toReal *
        Real.log ((π.map (fun γ => γ t)).rnDeriv μ x).toReal) μ := by
  let : IsFiniteMeasure (μ.restrict (closedBall p (3*R))) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall p (3*R)).measure_lt_top.ne
  have hstay : ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ closedBall p (3*R) := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ π hg hp p hR hs₀ hs₁).mono fun γ hγ => hγ.2 t
  have he := entropy_integrable_of_bounded_support μ (π.map (fun γ => γ t))
    ENNReal.ofReal_ne_top (hc t) measurableSet_closedBall hstay
  have ha : π.map (fun γ => γ t) ≪ μ.restrict (closedBall p (3*R)) :=
    Measure.absolutelyContinuous_of_le_smul ((compression_iff_localized μ _ hstay _).mp (hc t))
  exact ⟨boltzmannEntropy_ge_neg_log_support μ _ measurableSet_closedBall ha he,
    boltzmannEntropy_le_log_density μ _ hC (hc t) he,he⟩

end RegularPointCoordinates

end

end OAI
