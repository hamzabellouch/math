import OAI.Geometry.RCD.Transport.OptimalMidpointSplice

namespace OAI

/-! # Exact path laws of an optimal midpoint splice

The gluing construction retains each entire half-path law. This lets
geometric length bounds pass to a replacement, beyond its one-time marginals.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X] [Nonempty X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] [SeparableSpace X] [CompleteSpace X] [Nonempty X] in
theorem joinMatched_subpath_left (z : MatchedPaths X) :
    subpath 0 midpointTime (joinMatched z)=z.val.1 := by
  ext t
  exact joinMatched_lowerTime z t

omit [MeasurableSpace X] [BorelSpace X] [SeparableSpace X] [CompleteSpace X] [Nonempty X] in
theorem joinMatched_subpath_right (z : MatchedPaths X) :
    subpath midpointTime 1 (joinMatched z)=z.val.2 := by
  ext t
  exact joinMatched_upperTime z t

theorem exists_optimal_midpoint_splice_exact
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
      τ.map (subpath 0 midpointTime)=q₀ ∧ τ.map (subpath midpointTime 1)=q₁ := by
  have he₀ := optimalPlan_endpoints _ _ q₀ hp₀
  have he₁ := optimalPlan_endpoints _ _ q₁ hp₁
  obtain ⟨ρ,hρ,hρ₀,hρ₁⟩ := exists_matched_path_law q₀ q₁ (he₀.2.trans he₁.1.symm)
  let := hρ
  obtain ⟨hpτ,hgτ,_⟩ := midpoint_matched_law_optimal π hg hp hfin q₀ q₁ hg₀ hg₁ hp₀ hp₁ ρ hρ₀ hρ₁
  refine ⟨ρ.map joinMatched,inferInstance,hgτ,hpτ,?_,?_⟩
  · rw [Measure.map_map (subpath_measurable 0 midpointTime) joinMatched_continuous.measurable]
    simpa only [Function.comp_def,joinMatched_subpath_left] using hρ₀
  · rw [Measure.map_map (subpath_measurable midpointTime 1) joinMatched_continuous.measurable]
    simpa only [Function.comp_def,joinMatched_subpath_right] using hρ₁

end RegularPointCoordinates

end

end OAI
