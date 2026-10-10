import OAI.Geometry.RCD.Heat.CompactHeatHarmonicAffineMean
import OAI.Geometry.RCD.Heat.CompactHeatActualPlanLimit
import OAI.Geometry.RCD.Sobolev.ContinuousPathMean

namespace OAI

/-! # One actual optimal plan with exact original harmonic-coordinate means -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {n : ℕ} {hX : NoncollapsedRCD 0 n X} {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

attribute [local instance] pathBorel pathBorelSpace

include D in
theorem exists_original_harmonic_affine_plan (a₀ : S) (b₀ : T)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R) (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R) :
    ∃ (π : ProbabilityMeasure C(Time,X)) (B : ℝ≥0∞), B ≠ ∞ ∧
      (∀ᵐ γ ∂(π : Measure C(Time,X)), IsGeodesic γ) ∧
      IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
        ((π : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))) ∧
      (∀ t : Time, (π.map (fun γ => γ t) : Measure X) ≤ B • hausdorff n X) ∧
      ∀ (u : SobolevSpace (hausdorff n X) hX.quadratic) (d : Lp ℝ 2 (hausdorff n X))
    (_hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    (U : X → ℝ) (L A : ℝ≥0) (_hU : LipschitzWith L U) (_hUc : HasCompactSupport U)
    (_hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] U)
    (_hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x| ≤ A)
    {b : ℝ} (_hb : 24*R < b)
    (_hd0 : d =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => 0) (c : ℝ)
    (_hc : localGamma (hausdorff n X) hX.quadratic u u
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => c),
      ∀ t : Time, (∫ x, U x ∂(π.map (fun γ => γ t) : Measure X)) =
        (1-(t:ℝ))*(∫ x : S, U x ∂μ)+(t:ℝ)*(∫ x : T, U x ∂ν) := by
  obtain ⟨π,j,B,c,hj,hB,hgeo,hopt,_hlen,hcomp,_hfor,_hback,hlim,_hcal⟩ :=
    exists_actual_heat_limit_plan (K := 0) D a₀ b₀ le_rfl hε1 hε0 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
      hC₀ hC₁ hμ hν hR hS hT
  refine ⟨π,B,hB,hgeo,hopt,hcomp,?_⟩
  intro u d hd U L A hU hUc hu hA b hb hd0 c hc
  let Q₀ (t : Ioo (0:ℝ) 1) := π.map (fun γ => γ (⟨t,t.property.1.le,t.property.2.le⟩ : Time))
  obtain ⟨α,β,haff⟩ := D.affine_original_harmonic_mean a₀ b₀ hε1 hε0
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT j hj Q₀
    (fun t => (hlim t).1) u d hd U L A hU hUc hu hA hb hd0 c hc
  obtain ⟨M,hM⟩ := hUc.exists_bound_of_continuous hU.continuous
  let F (t : Time) := ∫ x, U x ∂(π.map (fun γ => γ t) : Measure X)
  have hFeq (t : Time) : F t=∫ γ, U (γ t) ∂(π : Measure C(Time,X)) := by
    exact integral_map (measurable_path_eval t).aemeasurable hU.continuous.aestronglyMeasurable
  have hcont : Continuous F := (continuous_path_mean (π : Measure C(Time,X)) U hU.continuous M
    (fun x => by simpa only [Real.norm_eq_abs] using hM x)).congr (fun t => (hFeq t).symm)
  have hclosed := closed_time_affine F hcont α β (fun t ht0 ht1 => by
    simpa only [F,Q₀] using haff ⟨t,ht0,ht1⟩)
  have hends := optimalPlan_endpoints (μ.map Subtype.val) (ν.map Subtype.val)
    (π : Measure C(Time,X)) hopt
  have h0 : F 0=∫ x:S, U x ∂μ := by
    change (∫ x, U x ∂((π : Measure C(Time,X)).map (fun γ => γ 0))) = _
    rw [hends.1]
    exact integral_map measurable_subtype_coe.aemeasurable hU.continuous.aestronglyMeasurable
  have h1 : F 1=∫ x:T, U x ∂ν := by
    change (∫ x, U x ∂((π : Measure C(Time,X)).map (fun γ => γ 1))) = _
    rw [hends.2]
    exact integral_map measurable_subtype_coe.aemeasurable hU.continuous.aestronglyMeasurable
  simpa only [F,h0,h1] using hclosed

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
