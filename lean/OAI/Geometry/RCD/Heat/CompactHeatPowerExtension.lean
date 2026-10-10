import OAI.Geometry.RCD.Heat.BoundedHeatPowerMean
import OAI.Geometry.RCD.Heat.CompactHeatInitialProduct
import OAI.Geometry.RCD.Heat.CompactHeatPowerDerivative

namespace OAI

/-! # Continuous extension of the actual power means to their initial values -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
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

theorem continuous_power_extension
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (k j : ℕ) :
    ∃ F : ℝ → ℝ, Continuous F ∧
      (∀ t, 0 < t → t < 1 → F t = D.interpolationPowerMean univ (j+1) k t) ∧
      F 0 = ∫ x, (ρ₀ x)^(j+1) ∂hausdorff n X := by
  let m := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  let c := ε k/4
  have hc : 0 < c := div_pos (hε k) (by norm_num)
  obtain ⟨f,⟨A,hf⟩,hfe⟩ := hX.compact_heat_factor_L2 hn p μ ρ₀ hm₀ hp₀ hC₀ hμ (D.left k)
  obtain ⟨g,⟨B,hg⟩,hge⟩ := hX.compact_heat_factor_L2 hn p ν ρ₁ hm₁ hp₁ hC₁ hν (D.right k)
  let F := boundedHeatPowerMean m Q f g A B j c
  refine ⟨F,boundedHeatPowerMean_continuous m Q f g A B j c,?_,?_⟩
  · intro t ht ht1
    rw [show F t = ∫ x, (heatAt m Q (c*t) f x*heatAt m Q (c*(1-t)) g x)^(j+1) ∂m from
      boundedHeatPowerMean_eq_integral m Q f g A B hf hg j c t]
    simp only [interpolationPowerMean,setIntegral_univ]
    apply integral_congr_ae
    have hs : 0 < c*t := mul_pos hc ht
    have hr : 0 < c*(1-t) := mul_pos hc (sub_pos.mpr ht1)
    filter_upwards [kernelHeat_represents_L2 m Q hk hs f,kernelHeat_represents_L2 m Q hk hr g]
      with x hx hy
    rw [← hx,← hy,← hfe (c*t) hs x,← hge (c*(1-t)) hr x]
    rfl
  · rw [show F 0 = ∫ x, (heatAt m Q (c*0) f x*heatAt m Q (c*(1-0)) g x)^(j+1) ∂m from
      boundedHeatPowerMean_eq_integral m Q f g A B hf hg j c 0]
    simp only [mul_zero,sub_zero,mul_one,heatAt_zero,one_apply_eq_self]
    apply integral_congr_ae
    exact (D.initial_heat_product ρ₀ hm₀ hp₀ hC₀ hμ k f g hfe hge).mono
      fun x hx => congrArg (fun a : ℝ => a^(j+1)) hx

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
