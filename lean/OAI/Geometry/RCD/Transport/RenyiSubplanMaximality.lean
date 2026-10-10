import OAI.Geometry.RCD.Transport.RenyiTreeMaximality
import OAI.Geometry.RCD.Transport.RenyiDisjointAdditivity

namespace OAI

/-! # Maximality passes to separated transport components

Replacing a subplan preserves optimality. If both the original component
and its replacement are disjoint from the untouched midpoint mass, exact
Rényi additivity transfers maximality to that component.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem RenyiMaximizingPlan.subplan_comparison
    (μ : Measure X) [IsFiniteMeasure μ] {ν₀ ν₁ : Measure X} [IsProbabilityMeasure ν₀]
    {π κ τ : Measure C(Time,X)} [IsProbabilityMeasure π] [IsFiniteMeasure τ]
    {t : Time} {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    (hmax : RenyiMaximizingPlan μ ν₀ ν₁ π t q)
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    (hκ : κ≤π)
    (ht : IsOptimalCoupling (κ.map (fun γ => γ 0)) (κ.map (fun γ => γ 1))
      (τ.map (fun γ => (γ 0,γ 1))))
    (hgt : ∀ᵐ γ ∂τ, IsGeodesic γ)
    (hsκ : (π-κ).map (fun γ => γ t) ⟂ₘ κ.map (fun γ => γ t))
    (hsτ : (π-κ).map (fun γ => γ t) ⟂ₘ τ.map (fun γ => γ t)) :
    (∫ x, ((τ.map (fun γ => γ t)).rnDeriv μ x).toReal^q ∂μ) ≤
      ∫ x, ((κ.map (fun γ => γ t)).rnDeriv μ x).toReal^q ∂μ := by
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  obtain ⟨hr,hgr,hpr⟩ := optimalPlan_replace_subplan hp hg hκ ht hgt
  have hm := hmax (π-κ+τ) hr hgr hpr
  have he : π.map (fun γ => γ t) =
      (π-κ).map (fun γ => γ t)+κ.map (fun γ => γ t) := by
    rw [←Measure.map_add _ _ (measurable_path_eval t),Measure.sub_add_cancel_of_le hκ]
  rw [Measure.map_add _ _ (measurable_path_eval t),he,
    renyiPower_add_mutuallySingular μ _ _ hsτ hq0 hq1,
    renyiPower_add_mutuallySingular μ _ _ hsκ hq0 hq1] at hm
  linarith

end RegularPointCoordinates

end

end OAI
