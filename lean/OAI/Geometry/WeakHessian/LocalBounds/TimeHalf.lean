import Mathlib
import OAI.Geometry.WeakHessian.Geodesics.MidpointSigmaLower

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

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

section MidpointBounds
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def timeHalf : Time := ⟨1/2, by norm_num, by norm_num⟩

lemma cd_midpoint_support_lower {m μ₀ μ₁ : Measure X} {π : Measure (Curve X)}
    [IsProbabilityMeasure π] {K N D : ℝ} (hN : 1 < N) (hD : 0 ≤ D)
    {C : ℝ≥0∞} (hends : IsCoupling (endpointCoupling π) μ₀ μ₁)
    (hd₀ : ∀ᵐ x ∂μ₀, μ₀.rnDeriv m x ≤ C)
    (hd₁ : ∀ᵐ x ∂μ₁, μ₁.rnDeriv m x ≤ C)
    (hlen : ∀ᵐ γ ∂π, dist (γ timeZero) (γ timeOne) ≤ D)
    (hcd : (∫⁻ γ, tauCoeff K N (1/2) (dist (γ timeZero) (γ timeOne)) *
        (μ₀.rnDeriv m (γ timeZero))^(-1/N) +
        tauCoeff K N (1/2) (dist (γ timeZero) (γ timeOne)) *
        (μ₁.rnDeriv m (γ timeOne))^(-1/N) ∂π) ≤ renyiIntegral m (interpolation π timeHalf) N)
    {A : Set X} (hA : MeasurableSet A) (hs : interpolation π timeHalf Aᶜ = 0) :
    ((2 : ℝ≥0∞)*midpointTauLower K N D)^N / C ≤ m A := by
  have hNp : 0 < N := by linarith
  have he₀ : ∀ᵐ γ ∂π, μ₀.rnDeriv m (γ timeZero) ≤ C := by
    apply ae_of_ae_map (p := fun x => μ₀.rnDeriv m x ≤ C) (continuous_eval_const timeZero).measurable.aemeasurable
    change ∀ᵐ x ∂interpolation π timeZero, μ₀.rnDeriv m x ≤ C
    rw [hends.interpolation_endpoints.1]
    exact hd₀
  have he₁ : ∀ᵐ γ ∂π, μ₁.rnDeriv m (γ timeOne) ≤ C := by
    apply ae_of_ae_map (p := fun x => μ₁.rnDeriv m x ≤ C) (continuous_eval_const timeOne).measurable.aemeasurable
    change ∀ᵐ x ∂interpolation π timeOne, μ₁.rnDeriv m x ≤ C
    rw [hends.interpolation_endpoints.2]
    exact hd₁
  have hneg {r : ℝ≥0∞} (hr : r ≤ C) : C^(-1/N) ≤ r^(-1/N) := by
    rw [show -1/N = -(1/N) by ring, ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hr (by positivity))
  let : IsProbabilityMeasure (interpolation π timeHalf) := interpolation_probability π timeHalf
  have hbase : (2:ℝ≥0∞)*midpointTauLower K N D*C^(-1/N) ≤ (m A)^(1/N) := by
    apply le_trans ?_ (hcd.trans (renyiIntegral_le_support hA hs hN))
    calc
      (2:ℝ≥0∞)*midpointTauLower K N D*C^(-1/N) =
        ∫⁻ _ : Curve X, midpointTauLower K N D*C^(-1/N)+midpointTauLower K N D*C^(-1/N) ∂π := by
          simp only [lintegral_const,measure_univ,mul_one]
          rw [two_mul,add_mul]
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [he₀,he₁,hlen] with γ h0 h1 hL
        have ht := tauCoeff_midpoint_lower (K := K) hN hD dist_nonneg hL
        exact add_le_add (mul_le_mul' ht (hneg h0)) (mul_le_mul' ht (hneg h1))
  have H := ENNReal.rpow_le_rpow hbase hNp.le
  have hp : (1/N)*N = 1 := by field_simp
  have hn : (-1/N)*N = -1 := by field_simp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hNp.le,← ENNReal.rpow_mul,hn,ENNReal.rpow_neg_one,
    ← ENNReal.rpow_mul,hp,ENNReal.rpow_one] at H
  exact H

end MidpointBounds

open MeasureTheory Set
open scoped ENNReal NNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma map_sub_of_le (μ ρ : Measure X) [IsFiniteMeasure ρ]
    (hρ : ρ ≤ μ) {f : X → Y} (hf : Measurable f) :
    (μ-ρ).map f = μ.map f - ρ.map f := by
  calc
    (μ-ρ).map f = ((μ-ρ).map f+ρ.map f)-ρ.map f := Measure.add_sub_cancel.symm
    _ = μ.map f - ρ.map f := by rw [← Measure.map_add _ _ hf,Measure.sub_add_cancel_of_le hρ]

lemma replacement_map_eq (μ ρ β : Measure X) [IsFiniteMeasure ρ]
    (hρ : ρ ≤ μ) {f : X → Y} (hf : Measurable f) (hβ : β.map f = ρ.map f) :
    (μ-ρ+β).map f = μ.map f := by
  rw [Measure.map_add _ _ hf,hβ,← Measure.map_add _ _ hf,Measure.sub_add_cancel_of_le hρ]

lemma replacement_probability (μ ρ β : Measure X) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ρ] (hρ : ρ ≤ μ) (hβ : β univ = ρ univ) :
    IsProbabilityMeasure (μ-ρ+β) := by
  constructor
  rw [Measure.add_apply,hβ,← Measure.add_apply,Measure.sub_add_cancel_of_le hρ,measure_univ]

variable [MetricSpace X] [BorelSpace X]

lemma endpointCoupling_add (π ξ : Measure (Curve X)) :
    endpointCoupling (π+ξ) = endpointCoupling π+endpointCoupling ξ := by
  exact Measure.map_add _ _ ((continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable)

omit [BorelSpace X] in
lemma quadraticTransportCost_add (q q' : Measure (X×X)) :
    QuadraticTransportCost (q+q') = QuadraticTransportCost q + QuadraticTransportCost q' :=
  lintegral_add_measure _ _ _

lemma IsOptimalCoupling.reroute_plan {π θ ξ : Measure (Curve X)} {μ₀ μ₁ : Measure X}
    [IsFiniteMeasure θ] (hopt : IsOptimalCoupling (endpointCoupling π) μ₀ μ₁)
    (hθ : θ ≤ π)
    (hξ₀ : interpolation ξ timeZero = interpolation θ timeZero)
    (hξ₁ : interpolation ξ timeOne = interpolation θ timeOne)
    (hcost : QuadraticTransportCost (endpointCoupling ξ) ≤ QuadraticTransportCost (endpointCoupling θ)) :
    IsOptimalCoupling (endpointCoupling (π-θ+ξ)) μ₀ μ₁ := by
  have hends := hopt.1.interpolation_endpoints
  have hends' : interpolation (π-θ+ξ) timeZero = μ₀ ∧
      interpolation (π-θ+ξ) timeOne = μ₁ := by
    constructor
    · exact (replacement_map_eq π θ ξ hθ (continuous_eval_const timeZero).measurable hξ₀).trans hends.1
    · exact (replacement_map_eq π θ ξ hθ (continuous_eval_const timeOne).measurable hξ₁).trans hends.2
  have hc : IsCoupling (endpointCoupling (π-θ+ξ)) μ₀ μ₁ := by
    have hm : Measurable (fun γ : Curve X => (γ timeZero,γ timeOne)) := (continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable
    constructor
    · simpa only [endpointCoupling,Measure.map_map measurable_fst hm,Function.comp_def,
        interpolation] using hends'.1
    · simpa only [endpointCoupling,Measure.map_map measurable_snd hm,Function.comp_def,
        interpolation] using hends'.2
  refine ⟨hc,fun q hq => le_trans ?_ (hopt.2 q hq)⟩
  calc
    QuadraticTransportCost (endpointCoupling (π-θ+ξ)) =
        QuadraticTransportCost (endpointCoupling (π-θ)) + QuadraticTransportCost (endpointCoupling ξ) := by
      rw [endpointCoupling_add,quadraticTransportCost_add]
    _ ≤ QuadraticTransportCost (endpointCoupling (π-θ)) + QuadraticTransportCost (endpointCoupling θ) :=
      add_le_add le_rfl hcost
    _ = QuadraticTransportCost (endpointCoupling π) := by
      rw [← quadraticTransportCost_add,← endpointCoupling_add,Measure.sub_add_cancel_of_le hθ]

omit [MeasurableSpace X] [BorelSpace X] in
lemma geodesic_plan_reroute {π θ ξ : Measure (Curve X)}
    (hπ : ∀ᵐ γ ∂π, IsGeodesic γ) (hξ : ∀ᵐ γ ∂ξ, IsGeodesic γ) :
    ∀ᵐ γ ∂(π-θ+ξ), IsGeodesic γ := by
  rw [ae_add_measure_iff]
  exact ⟨(Measure.absolutelyContinuous_of_le Measure.sub_le).ae_le hπ,hξ⟩

lemma interpolation_restricted (π : Measure (Curve X)) (t : Time)
    {A : Set X} (hA : MeasurableSet A) :
    interpolation (π.restrict ((fun γ => γ t) ⁻¹' A)) t = (interpolation π t).restrict A := by
  exact (Measure.restrict_map (continuous_eval_const t).measurable hA).symm

end WeakHessian

end

end OAI
