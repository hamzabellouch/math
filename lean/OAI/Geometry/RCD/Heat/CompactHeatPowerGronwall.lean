import OAI.Geometry.RCD.Heat.CompactHeatPowerRateBound
import OAI.Geometry.RCD.Heat.CompactHeatPowerExtension
import OAI.Geometry.RCD.Harmonic.AffineGrowthOnInterval
import OAI.Geometry.RCD.Metric.ProbabilityDensityPowerBound

namespace OAI

/-! # Uniform exponential growth of the actual interpolation moments -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem interpolation_power_gronwall (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ a : S, dist z a ≤ R) (hT : ∀ b : T, dist z b ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k j : ℕ) (t : Ioo (0:ℝ) 1), (t:ℝ) ≤ 1/2 →
      (∫ x, (D.interpolationDensity k t x)^(j+2) ∂hausdorff n X)+1 ≤
        Real.exp (C*(j+1:ℝ)*t)*((C₀:ℝ)^(j+1)+1) := by
  obtain ⟨C,hC,hder⟩ := D.interpolationPowerMean_deriv_le hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
    hC₀ hC₁ hμ hν z hR hS hT
  refine ⟨C,hC,?_⟩
  intro k j t ht
  obtain ⟨F,hF,hFE,hF0⟩ := D.continuous_power_extension ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
    hC₀ hC₁ hμ hν k (j+1)
  have hgrow : F t+1 ≤ Real.exp (C*(j+1:ℝ)*t)*(F 0+1) := by
    apply affine_growth_on_interval (b := (1:ℝ)/2) (by norm_num) hF.continuousOn ?_
      ⟨t.property.1.le,ht⟩
    intro s hs
    obtain ⟨hd,hbound⟩ := hder k j s hs.1 hs.2
    have hloc : F =ᶠ[𝓝 s] D.interpolationPowerMean univ (j+2) k := by
      filter_upwards [Ioo_mem_nhds hs.1 (show s < 1 by linarith [hs.2])] with r hr
      simpa only [Nat.add_assoc] using hFE r hr.1 hr.2
    have hdiff := hd.hasDerivAt.congr_of_eventuallyEq hloc
    refine ⟨hdiff.differentiableAt,?_⟩
    rw [hdiff.deriv,hloc.eq_of_nhds]
    exact hbound
  have he : F t = ∫ x, (D.interpolationDensity k t x)^(j+2) ∂hausdorff n X := by
    rw [hFE t t.property.1 t.property.2]
    simp only [interpolationPowerMean,setIntegral_univ]
    rfl
  rw [he,hF0] at hgrow
  let : IsProbabilityMeasure ((hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x))) := by
    rw [← hμ]
    infer_instance
  have hinit := probability_density_power_bound (hausdorff n X) hm₀ hp₀ C₀ hC₀ (j+1)
  simp only [Nat.add_assoc] at hgrow hinit
  exact hgrow.trans (mul_le_mul_of_nonneg_left (add_le_add hinit le_rfl) (Real.exp_pos _).le)

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
