import OAI.Geometry.RCD.Coordinates.HalfRestrictedMean

namespace OAI

/-! # Half-restricted optimal plans retain uniform compression -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem half_restricted_optimal_plan (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    (hfin : transportCost (π.map (fun γ => (γ 0,γ 1))) ≠ ∞)
    (μ : Measure X) {C : ℝ≥0∞} (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (p : X) {R : ℝ}
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R) (S : Set C(Time,X)) :
    let κ := halfRestrictedMeasure π S
    let ρ := (κ univ)⁻¹ • κ
    IsProbabilityMeasure ρ ∧ (∀ᵐ γ ∂ρ, IsGeodesic γ) ∧
      IsOptimalCoupling (ρ.map (fun γ => γ 0)) (ρ.map (fun γ => γ 1))
        (ρ.map (fun γ => (γ 0,γ 1))) ∧
      (∀ t : Time, ρ.map (fun γ => γ t) ≤ (2*C) • μ) ∧
      (∀ᵐ x ∂ρ.map (fun γ => γ 0), dist x p ≤ R) ∧
      (∀ᵐ x ∂ρ.map (fun γ => γ 1), dist x p ≤ R) := by
  intro κ ρ
  obtain ⟨hp,hg,ho,hcomp,hs0,hs1⟩ := normalized_subplan_data π hgeo hopt hfin μ hc p hs₀ hs₁
    κ (halfRestrictedMeasure_le π S) (halfRestrictedMeasure_mass_ne_zero π S)
  have hinv : (κ univ)⁻¹ ≤ 2 := by
    have hh := ENNReal.inv_le_inv.mpr (halfRestrictedMeasure_mass_lower π S)
    simpa only [one_div,inv_inv] using hh
  refine ⟨hp,hg,ho,?_,hs0,hs1⟩
  intro t
  apply (hcomp t).trans
  intro A
  exact mul_le_mul' (mul_le_mul' hinv le_rfl) le_rfl

end RegularPointCoordinates

end

end OAI
