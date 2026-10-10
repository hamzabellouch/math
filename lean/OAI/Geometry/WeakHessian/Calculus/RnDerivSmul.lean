import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.TimeHalf

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
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
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma rnDeriv_le_of_le_smul {m μ : Measure X} [SigmaFinite m] {C : ℝ≥0∞}
    (h : μ ≤ C • m) : ∀ᵐ x ∂m, μ.rnDeriv m x ≤ C := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv m)
  intro A _ _
  calc
    (∫⁻ x in A, μ.rnDeriv m x ∂m) ≤ μ A := Measure.setLIntegral_rnDeriv_le A
    _ ≤ C*m A := h A
    _ = ∫⁻ _ in A, C ∂m := by simp

lemma endpointCoupling_couples (π : Measure (Curve X)) :
    IsCoupling (endpointCoupling π) (interpolation π timeZero) (interpolation π timeOne) := by
  have hm : Measurable (fun γ : Curve X => (γ timeZero,γ timeOne)) := (continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable
  constructor
  · simp only [endpointCoupling,Measure.map_map measurable_fst hm,Function.comp_def,interpolation]
  · simp only [endpointCoupling,Measure.map_map measurable_snd hm,Function.comp_def,interpolation]

lemma CurvatureDimension.reroute_finite_subplan {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (θ : Measure (Curve X)) [IsFiniteMeasure θ] (hq : θ univ ≠ 0)
    (o : X) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ᵐ γ ∂θ, dist (γ timeZero) o ≤ R ∧ dist (γ timeOne) o ≤ R)
    {C : ℝ≥0∞} (hd₀ : interpolation θ timeZero ≤ C • m)
    (hd₁ : interpolation θ timeOne ≤ C • m) :
    ∃ ξ : Measure (Curve X), IsFiniteMeasure ξ ∧ ξ univ = θ univ ∧
      (∀ᵐ γ ∂ξ, IsGeodesic γ) ∧
      interpolation ξ timeZero = interpolation θ timeZero ∧
      interpolation ξ timeOne = interpolation θ timeOne ∧
      QuadraticTransportCost (endpointCoupling ξ) ≤ QuadraticTransportCost (endpointCoupling θ) ∧
      ∀ B : Set X, MeasurableSet B → interpolation ξ timeHalf Bᶜ = 0 →
        ((2:ℝ≥0∞)*midpointTauLower K N (2*R))^N / ((θ univ)⁻¹*C) ≤ m B := by
  let q := θ univ
  have hqt : q ≠ ∞ := measure_ne_top _ _
  let θ' : Measure (Curve X) := q⁻¹ • θ
  have hp : IsProbabilityMeasure θ' := by
    constructor
    change q⁻¹*θ univ = 1
    exact ENNReal.inv_mul_cancel hq hqt
  let := hp
  have hcanc : q • θ' = θ := by
    change q • (q⁻¹ • θ) = θ
    rw [smul_smul,ENNReal.mul_inv_cancel hq hqt,one_smul]
  let μ₀ := interpolation θ' timeZero
  let μ₁ := interpolation θ' timeOne
  let : IsProbabilityMeasure μ₀ := interpolation_probability θ' timeZero
  let : IsProbabilityMeasure μ₁ := interpolation_probability θ' timeOne
  have he (t : Time) : interpolation θ' t = q⁻¹ • interpolation θ t :=
    Measure.map_smul _ (continuous_eval_const t).measurable.aemeasurable
  have hd0 : μ₀ ≤ (q⁻¹*C) • m := by
    dsimp only [μ₀]
    rw [he,← smul_smul]
    exact smul_le_smul_left _ hd₀
  have hd1 : μ₁ ≤ (q⁻¹*C) • m := by
    dsimp only [μ₁]
    rw [he,← smul_smul]
    exact smul_le_smul_left _ hd₁
  have hac0 : μ₀ ≪ m := (Measure.absolutelyContinuous_of_le hd0).trans
    (Measure.AbsolutelyContinuous.rfl.smul_left _)
  have hac1 : μ₁ ≪ m := (Measure.absolutelyContinuous_of_le hd1).trans
    (Measure.AbsolutelyContinuous.rfl.smul_left _)
  have hb' : ∀ᵐ γ ∂θ', dist (γ timeZero) o ≤ R ∧ dist (γ timeOne) o ≤ R :=
    (Measure.AbsolutelyContinuous.rfl.smul_left _).ae_le hb
  have hb0 : ∀ᵐ x ∂μ₀, dist x o ≤ R :=
    (ae_map_iff (continuous_eval_const timeZero).measurable.aemeasurable
      (measurableSet_le (continuous_id.dist continuous_const).measurable measurable_const)).mpr
      (hb'.mono fun _ h => h.1)
  have hb1 : ∀ᵐ x ∂μ₁, dist x o ≤ R :=
    (ae_map_iff (continuous_eval_const timeOne).measurable.aemeasurable
      (measurableSet_le (continuous_id.dist continuous_const).measurable measurable_const)).mpr
      (hb'.mono fun _ h => h.2)
  obtain ⟨π,hπ,hgeo,hopt,hent⟩ := hcd μ₀ μ₁ inferInstance inferInstance
    (hasSecondMoment_of_ae_dist_le o R hb0) (hasSecondMoment_of_ae_dist_le o R hb1) hac0 hac1
  let := hπ
  obtain ⟨he0,he1⟩ := hopt.1.interpolation_endpoints
  have hπ0 : ∀ᵐ γ ∂π, dist (γ timeZero) o ≤ R := by
    apply ae_of_ae_map (f := fun γ : Curve X => γ timeZero) (p := fun x => dist x o ≤ R) (continuous_eval_const timeZero).measurable.aemeasurable
    change ∀ᵐ x ∂interpolation π timeZero, dist x o ≤ R
    rw [he0]
    exact hb0
  have hπ1 : ∀ᵐ γ ∂π, dist (γ timeOne) o ≤ R := by
    apply ae_of_ae_map (f := fun γ : Curve X => γ timeOne) (p := fun x => dist x o ≤ R) (continuous_eval_const timeOne).measurable.aemeasurable
    change ∀ᵐ x ∂interpolation π timeOne, dist x o ≤ R
    rw [he1]
    exact hb1
  have hlen : ∀ᵐ γ ∂π, dist (γ timeZero) (γ timeOne) ≤ 2*R := by
    filter_upwards [hπ0,hπ1] with γ h0 h1
    have H := dist_triangle (γ timeZero) o (γ timeOne)
    rw [dist_comm o (γ timeOne)] at H
    linarith
  let ξ := q • π
  have hξmass : ξ univ = θ univ := by simp [ξ,q]
  have hξfin : IsFiniteMeasure ξ := ⟨hξmass ▸ measure_lt_top θ univ⟩
  have hξend (t : Time) (ht : interpolation π t = interpolation θ' t) :
      interpolation ξ t = interpolation θ t := by
    change (q • π).map _ = _
    rw [Measure.map_smul _ (continuous_eval_const t).measurable.aemeasurable]
    change q • interpolation π t = _
    rw [ht]
    change q • θ'.map (fun γ => γ t) = θ.map (fun γ => γ t)
    rw [← Measure.map_smul _ (continuous_eval_const t).measurable.aemeasurable,hcanc]
  refine ⟨ξ,hξfin,hξmass,(Measure.AbsolutelyContinuous.rfl.smul_left _).ae_le hgeo,
    hξend timeZero he0,hξend timeOne he1,?_,?_⟩
  · have H := mul_le_mul' (le_refl q) (hopt.2 (endpointCoupling θ') (endpointCoupling_couples θ'))
    change q*QuadraticTransportCost (endpointCoupling π) ≤ q*QuadraticTransportCost (endpointCoupling θ') at H
    have hs (η : Measure (Curve X)) : QuadraticTransportCost (endpointCoupling (q • η)) =
        q*QuadraticTransportCost (endpointCoupling η) := by
      have hmeas : Measurable (fun γ : Curve X => (γ timeZero,γ timeOne)) :=
        (continuous_eval_const timeZero).measurable.prodMk
          (continuous_eval_const timeOne).measurable
      simp only [QuadraticTransportCost,endpointCoupling,
        Measure.map_smul _ hmeas.aemeasurable,lintegral_smul_measure,smul_eq_mul]
    rw [← hs π,← hs θ',hcanc] at H
    exact H
  · intro B hB hs
    have hs' : interpolation π timeHalf Bᶜ = 0 := by
      change (q • π).map _ Bᶜ = 0 at hs
      rw [Measure.map_smul _ (continuous_eval_const timeHalf).measurable.aemeasurable,
        Measure.smul_apply,smul_eq_mul] at hs
      exact (mul_eq_zero.mp hs).resolve_left hq
    apply cd_midpoint_support_lower hN (by linarith) hopt.1
      (hac0.ae_le (rnDeriv_le_of_le_smul hd0))
      (hac1.ae_le (rnDeriv_le_of_le_smul hd1)) hlen ?_ hB hs'
    simpa only [timeHalf, show (1 : ℝ)-1/2 = 1/2 by norm_num] using hent N le_rfl timeHalf

end WeakHessian

end
end InlinedFile0

end OAI
