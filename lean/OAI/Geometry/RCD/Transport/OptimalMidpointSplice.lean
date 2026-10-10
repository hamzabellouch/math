import OAI.Geometry.RCD.Transport.CanonicalRenyiConstruction

namespace OAI

/-! # Splicing an optimal half-plan while preserving the other half

This interface retains the complete family of marginals on each half,
including the shared midpoint needed for length-class localization.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X] [Nonempty X]
attribute [local instance] pathBorel pathBorelSpace

theorem exists_optimal_midpoint_splice
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    (hfin : transportCost (π.map (fun γ => (γ 0,γ 1)))≠∞)
    (q₀ q₁ : Measure C(Time,X)) [IsProbabilityMeasure q₀] [IsProbabilityMeasure q₁]
    (hg₀ : ∀ᵐ γ ∂q₀, IsGeodesic γ) (hg₁ : ∀ᵐ γ ∂q₁, IsGeodesic γ)
    (hp₀ : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ midpointTime))
      (q₀.map (fun γ => (γ 0,γ 1))))
    (hp₁ : IsOptimalCoupling (π.map (fun γ => γ midpointTime)) (π.map (fun γ => γ 1))
      (q₁.map (fun γ => (γ 0,γ 1)))) :
    ∃ τ : Measure C(Time,X), IsProbabilityMeasure τ ∧
      (∀ᵐ γ ∂τ, IsGeodesic γ) ∧
      IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
        (τ.map (fun γ => (γ 0,γ 1))) ∧
      (∀ t, τ.map (fun γ => γ (lowerTime t))=q₀.map (fun γ => γ t)) ∧
      (∀ t, τ.map (fun γ => γ (upperTime t))=q₁.map (fun γ => γ t)) := by
  have he₀ := optimalPlan_endpoints _ _ q₀ hp₀
  have he₁ := optimalPlan_endpoints _ _ q₁ hp₁
  obtain ⟨ρ,hρ,hρ₀,hρ₁⟩ := exists_matched_path_law q₀ q₁ (he₀.2.trans he₁.1.symm)
  let := hρ
  obtain ⟨hpτ,hgτ,_⟩ := midpoint_matched_law_optimal π hg hp hfin q₀ q₁ hg₀ hg₁ hp₀ hp₁ ρ hρ₀ hρ₁
  exact ⟨ρ.map joinMatched,inferInstance,hgτ,hpτ,
    joined_law_eval_lowerTime ρ q₀ hρ₀,joined_law_eval_upperTime ρ q₁ hρ₁⟩

theorem exists_optimal_left_splice
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    (hfin : transportCost (π.map (fun γ => (γ 0,γ 1)))≠∞)
    (q : Measure C(Time,X)) [IsProbabilityMeasure q]
    (hgq : ∀ᵐ γ ∂q, IsGeodesic γ)
    (hpq : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ midpointTime))
      (q.map (fun γ => (γ 0,γ 1)))) :
    ∃ τ : Measure C(Time,X), IsProbabilityMeasure τ ∧
      (∀ᵐ γ ∂τ, IsGeodesic γ) ∧
      IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
        (τ.map (fun γ => (γ 0,γ 1))) ∧
      (∀ t, τ.map (fun γ => γ (lowerTime t))=q.map (fun γ => γ t)) ∧
      (∀ t, τ.map (fun γ => γ (upperTime t))=π.map (fun γ => γ (upperTime t))) := by
  obtain ⟨hq₁,hg₁,hp₁⟩ := geodesic_subpath_law π hg hp hfin midpointTime 1
  let := hq₁
  obtain ⟨τ,hτ,hgτ,hpτ,hl,hr⟩ := exists_optimal_midpoint_splice π hg hp hfin
    q (π.map (subpath midpointTime 1)) hgq hg₁ hpq hp₁
  refine ⟨τ,hτ,hgτ,hpτ,hl,?_⟩
  intro t
  exact (hr t).trans (subpath_map_eval π midpointTime 1 t)

end RegularPointCoordinates

end

end OAI
