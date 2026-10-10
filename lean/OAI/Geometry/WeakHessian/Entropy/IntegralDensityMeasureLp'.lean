import Mathlib
import OAI.Geometry.WeakHessian.Transport.TestPlanCostReference
import OAI.Geometry.WeakHessian.Sobolev.EndpointPairingBoundGlobal

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
open WeakHessianFunctional WeakHessianTransport MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m ν : Measure X} [IsProbabilityMeasure ν]

omit [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X]
  [IsProbabilityMeasure ν] in
lemma integral_densityMeasure_lp' (ρ : Lp ℝ 2 ν) (hρ : ∀ᵐ x ∂ν,0 ≤ ρ x) (f : Lp ℝ 2 ν) :
    (∫ x,f x ∂densityMeasure ν ρ) = ⟪f,ρ⟫_ℝ := by
  rw [integral_densityMeasure ν ρ hρ,L2.inner_def]
  simp only [RCLike.inner_apply,conj_trivial]

lemma CurvatureDimension.prox_weak_pairing_perturbed {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {u v D : Lp ℝ 2 ν} {t : ℝ} (h : RelaxedProx u t v D)
    (hmass : ∫ x,u x ∂ν = 0) {ε B : ℝ}
    (hε : 0 < ε) (hB : 0 ≤ B) (hεB : ε*B < 1)
    (hu : ∀ᵐ x ∂ν, |u x| ≤ B) (hv : ∀ᵐ x ∂ν, |v x| ≤ B)
    {f W : Lp ℝ 2 ν} (hf : IsLocalWeakUpperGradient ν (f : X → ℝ) (W : X → ℝ)) :
    |⟪f,u-v⟫_ℝ| ≤ Real.sqrt (1+ε*B)*‖W‖*(t^2*‖D‖)/Real.sqrt (1-ε*B) := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure ν
  obtain ⟨π,hπ,hmarg,hcomp,hact⟩ := hcd.prox_testPlan hν h hmass hε.le hB hεB hu hv
  let C : ℝ≥0 := ⟨1+ε*B,by positivity⟩
  have hC (r : Time) : π.map (fun γ => γ r) ≤ (C:ℝ≥0∞) • ν := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact hcomp r
  have H := hf.endpoint_pairing_bound_global hπ hC
    (by positivity : 0 ≤ ε^2/(1-ε*B)*(t^2*‖D‖)^2) hact
  rw [hmarg timeOne,hmarg timeZero] at H
  have hpos (r : Time) : ∀ᵐ x ∂ν,0 ≤ linearDensity ε u v r x :=
    (linearDensity_bounds hε.le hB r.2 hu hv).mono fun _ hx => (sub_pos.mpr hεB).le.trans hx.1
  rw [integral_densityMeasure_lp' _ (hpos timeOne),integral_densityMeasure_lp' _ (hpos timeZero)] at H
  have hl : |⟪f,linearDensity ε u v timeOne⟫_ℝ-⟪f,linearDensity ε u v timeZero⟫_ℝ| =
      ε*|⟪f,u-v⟫_ℝ| := by
    simp only [linearDensity,timeOne,timeZero,one_smul,zero_smul,add_zero,
      inner_add_right,real_inner_smul_right,inner_sub_right]
    rw [show ⟪f,constLp 1⟫_ℝ+ε*(⟪f,u⟫_ℝ+(⟪f,v⟫_ℝ-⟪f,u⟫_ℝ))-
      (⟪f,constLp 1⟫_ℝ+ε*⟪f,u⟫_ℝ) = ε*(⟪f,v⟫_ℝ-⟪f,u⟫_ℝ) by ring]
    rw [abs_mul,abs_of_pos hε,abs_sub_comm]
  rw [hl] at H
  have hr : Real.sqrt (ε^2/(1-ε*B)*(t^2*‖D‖)^2) = ε*(t^2*‖D‖)/Real.sqrt (1-ε*B) := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ ε^2/(1-ε*B)),Real.sqrt_div (sq_nonneg ε),
      Real.sqrt_sq hε.le,Real.sqrt_sq (by positivity : 0 ≤ t^2*‖D‖)]
    ring
  rw [hr] at H
  change ε*|⟪f,u-v⟫_ℝ| ≤ Real.sqrt (1+ε*B)*‖W‖*(ε*(t^2*‖D‖)/Real.sqrt (1-ε*B)) at H
  apply (mul_le_mul_iff_right₀ hε).mp
  calc
    ε*|⟪f,u-v⟫_ℝ| ≤ Real.sqrt (1+ε*B)*‖W‖*(ε*(t^2*‖D‖)/Real.sqrt (1-ε*B)) := H
    _ = ε*(Real.sqrt (1+ε*B)*‖W‖*(t^2*‖D‖)/Real.sqrt (1-ε*B)) := by ring

lemma CurvatureDimension.prox_weak_pairing_centered {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {u v D : Lp ℝ 2 ν} {t : ℝ} (h : RelaxedProx u t v D)
    (hmass : ∫ x,u x ∂ν = 0) {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ᵐ x ∂ν,|u x| ≤ B) (hv : ∀ᵐ x ∂ν,|v x| ≤ B)
    {f W : Lp ℝ 2 ν} (hf : IsLocalWeakUpperGradient ν (f : X → ℝ) (W : X → ℝ)) :
    |⟪f,u-v⟫_ℝ| ≤ t^2*‖D‖*‖W‖ := by
  have hc : ContinuousAt (fun ε : ℝ => Real.sqrt (1+ε*B)*‖W‖*(t^2*‖D‖)/Real.sqrt (1-ε*B)) 0 := by
    fun_prop (disch := norm_num)
  have hl : Tendsto (fun ε : ℝ => Real.sqrt (1+ε*B)*‖W‖*(t^2*‖D‖)/Real.sqrt (1-ε*B))
      (𝓝[>] 0) (𝓝 (t^2*‖D‖*‖W‖)) := by
    simpa [mul_comm] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hl
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0,ε*B < 1 := by
    have H : Tendsto (fun ε : ℝ => ε*B) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 (0:ℝ)) (𝓝 0)).mono_left nhdsWithin_le_nhds).mul_const B
    exact H.eventually_lt_const zero_lt_one
  filter_upwards [hb,self_mem_nhdsWithin] with ε hεB hε
  exact hcd.prox_weak_pairing_perturbed hν h hmass hε hB hεB hu hv hf
end WeakHessian

end
end InlinedFile0

end OAI
