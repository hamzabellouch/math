import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatDensityCouplingCost
import OAI.Geometry.WeakHessian.Sobolev.EndpointPairingBound

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Bornology
open scoped Topology
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology


open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] (m : Measure X)

local instance : Algebra ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) := Algebra.complexToReal

local instance : Algebra ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) := Algebra.complexToReal

local instance : Algebra ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) := Algebra.complexToReal

local instance : Algebra ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) := Algebra.complexToReal

end WeakHessianFunctional

open Set Filter
open scoped Topology ENNReal NNReal


open Set


open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal


open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


namespace WeakHessian
open WeakHessianFunctional WeakHessianTransport MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X} [IsProbabilityMeasure m]

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure m] in
lemma integral_densityMeasure_lp (ρ : Lp ℝ 2 m) (hρ : ∀ᵐ x ∂m, 0 ≤ ρ x) (f : Lp ℝ 2 m) :
    (∫ x, f x ∂densityMeasure m ρ) = ⟪f,ρ⟫_ℝ := by
  rw [integral_densityMeasure m ρ hρ, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]

lemma CurvatureDimension.heatDensity_weak_increment {K N : ℝ} (hcd : CurvatureDimension m K N)
    (h : QuadraticCheegerEnergy m)
    {u A : Lp ℝ 2 m} (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hmass : ∫ x, u x ∂m = 0) {ε B b : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hεB : ε*B < 1)
    (hub : ∀ᵐ x ∂m, |u x| ≤ B) (hb : 0 ≤ b)
    {f D : Lp ℝ 2 m} (hf : IsLocalWeakUpperGradient m (f : X → ℝ) (D : X → ℝ)) :
    |⟪f,heatDensity h ε u b⟫_ℝ-⟪f,heatDensity h ε u 0⟫_ℝ| ≤
      ε*b*(Real.sqrt (1+ε*B)*‖D‖*Real.sqrt (2/(1-ε*B)*(cheegerEnergy m (u : X → ℝ)).toReal)) := by
  obtain ⟨π,hπ,htrack,hmarg,hcomp,hact⟩ := hcd.heatDensity_testPlan h hu hmass hε hB hεB hub hb
  let C : ℝ≥0 := ⟨1+ε*B,by positivity⟩
  have hC (r : Time) : π.map (fun γ => γ r) ≤ (C:ℝ≥0∞) • m := by
    convert hcomp r using 1
    congr 1
    exact (ENNReal.ofReal_eq_coe_nnreal (by positivity : 0 ≤ 1+ε*B)).symm
  have HH := hf.endpoint_pairing_bound hπ htrack hC
    (by positivity : 0 ≤ (2*ε^2/(1-ε*B)*(cheegerEnergy m (u : X → ℝ)).toReal)*b^2) hact
  rw [hmarg timeOne, hmarg timeZero] at HH
  simp only [timeOne, timeZero, mul_one, mul_zero] at HH
  have hpos (t : ℝ) (ht : 0 ≤ t) : ∀ᵐ x ∂m, 0 ≤ heatDensity h ε u t x :=
    (heatDensity_bounds h hε hB ht u hub).mono fun _ hx => (sub_pos.mpr hεB).le.trans hx.1
  rw [integral_densityMeasure_lp _ (hpos b hb), integral_densityMeasure_lp _ (hpos 0 le_rfl)] at HH
  apply HH.trans_eq
  change Real.sqrt (1+ε*B)*‖D‖*Real.sqrt _ = _
  have he : (2*ε^2/(1-ε*B)*(cheegerEnergy m (u : X → ℝ)).toReal)*b^2 =
      (ε*b)^2*(2/(1-ε*B)*(cheegerEnergy m (u : X → ℝ)).toReal) := by ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hε hb)]
  ring

lemma CurvatureDimension.weak_generator_pairing_perturbed {K N : ℝ} (hcd : CurvatureDimension m K N)
    (h : QuadraticCheegerEnergy m)
    {u A : Lp ℝ 2 m} (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hmass : ∫ x, u x ∂m = 0) {ε B : ℝ}
    (hε : 0 < ε) (hB : 0 ≤ B) (hεB : ε*B < 1)
    (hub : ∀ᵐ x ∂m, |u x| ≤ B)
    {f D : Lp ℝ 2 m} (hf : IsLocalWeakUpperGradient m (f : X → ℝ) (D : X → ℝ)) :
    |⟪f,A⟫_ℝ| ≤ Real.sqrt (1+ε*B)*‖D‖*Real.sqrt (2/(1-ε*B)*(cheegerEnergy m (u : X → ℝ)).toReal) := by
  have hg := heatDensity_affine_deriv h ε hu (s := 0) (d := 1) (r := 0) le_rfl zero_le_one le_rfl
  have hd : HasDerivWithinAt (fun t => ⟪f,heatDensity h ε u t⟫_ℝ) (ε*⟪f,A⟫_ℝ) (Ici 0) 0 := by
    have H := (hasDerivWithinAt_const (0:ℝ) (Ici 0) f).inner ℝ hg
    simpa only [one_mul, zero_add, mul_one, mul_zero, cheegerHeat_zero,
      one_apply_eq_self, real_inner_smul_right, inner_zero_left, add_zero] using! H
  have hl : Tendsto (fun b : ℝ => |slope (fun t => ⟪f,heatDensity h ε u t⟫_ℝ) 0 b|)
      (𝓝[>] (0:ℝ)) (𝓝 |ε*⟪f,A⟫_ℝ|) := by
    exact ((hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp
      hd.Ioi_of_Ici).abs
  have Hle : |ε*⟪f,A⟫_ℝ| ≤ ε*(Real.sqrt (1+ε*B)*‖D‖*
      Real.sqrt (2/(1-ε*B)*(cheegerEnergy m (u : X → ℝ)).toReal)) := by
    apply le_of_tendsto hl
    filter_upwards [self_mem_nhdsWithin] with b hb
    have hb' : (0:ℝ) < b := hb
    have HH := hcd.heatDensity_weak_increment h hu hmass hε.le hB hεB hub hb'.le hf
    rw [slope_def_field, sub_zero, abs_div, abs_of_pos hb']
    exact (div_le_iff₀ hb').mpr (by nlinarith [HH])
  rw [abs_mul, abs_of_pos hε] at Hle
  exact (mul_le_mul_iff_right₀ hε).mp Hle

lemma CurvatureDimension.weak_generator_pairing_centered {K N : ℝ} (hcd : CurvatureDimension m K N)
    (h : QuadraticCheegerEnergy m)
    {u A : Lp ℝ 2 m} (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hmass : ∫ x, u x ∂m = 0) {B : ℝ} (hB : 0 ≤ B)
    (hub : ∀ᵐ x ∂m, |u x| ≤ B)
    {f D : Lp ℝ 2 m} (hf : IsLocalWeakUpperGradient m (f : X → ℝ) (D : X → ℝ)) :
    |⟪f,A⟫_ℝ| ≤ Real.sqrt (2*(cheegerEnergy m (u : X → ℝ)).toReal)*‖D‖ := by
  let E := (cheegerEnergy m (u : X → ℝ)).toReal
  have hc : ContinuousAt (fun ε : ℝ => Real.sqrt (1+ε*B)*‖D‖*Real.sqrt (2/(1-ε*B)*E)) 0 := by
    fun_prop (disch := norm_num)
  have hl : Tendsto (fun ε : ℝ => Real.sqrt (1+ε*B)*‖D‖*Real.sqrt (2/(1-ε*B)*E))
      (𝓝[>] 0) (𝓝 (Real.sqrt (2*E)*‖D‖)) := by
    simpa [mul_comm] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hl
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε*B < 1 := by
    have H : Tendsto (fun ε : ℝ => ε*B) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 (0:ℝ)) (𝓝 0)).mono_left nhdsWithin_le_nhds).mul_const B
    exact H.eventually_lt_const zero_lt_one
  filter_upwards [hb,self_mem_nhdsWithin] with ε hεB hε
  exact hcd.weak_generator_pairing_perturbed h hu hmass hε hB hεB hub hf

end WeakHessian

end

end OAI
