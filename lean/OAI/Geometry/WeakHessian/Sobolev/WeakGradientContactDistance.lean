import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.AscendingSlope

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
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X}

lemma weakGradient_le_contact_distance (hfinite : FiniteOnBoundedSets m)
    {φ ψ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    {q : Measure (X × X)} (hq : q.map Prod.fst ≪ m)
    (hcontact : ∀ᵐ z ∂q, φ z.1+ψ z.2 = dist z.1 z.2^2/2) :
    ∀ᵐ z ∂q, weakGradient m φ z.1 ≤ dist z.1 z.2 := by
  have H := hq.ae_le (weakGradient_le_ascendingSlope hfinite hφ)
  have H' := ae_of_ae_map measurable_fst.aemeasurable H
  filter_upwards [H',hcontact] with z hz hc
  apply hz.trans
  have hb := ascendingSlope_contact hdual hc
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal dist_nonneg)

lemma weakGradient_contact_action_le (hfinite : FiniteOnBoundedSets m)
    {φ ψ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    {q : Measure (X × X)} (hq : q.map Prod.fst ≪ m)
    (hcontact : ∀ᵐ z ∂q, φ z.1+ψ z.2 = dist z.1 z.2^2/2) :
    (∫⁻ x, (ENNReal.ofReal (weakGradient m φ x))^2 ∂(q.map Prod.fst)) ≤
      ∫⁻ z, (edist z.1 z.2)^2 ∂q := by
  have hmeas : AEMeasurable (weakGradient m φ) m := by
    by_cases h : ∃ D, IsMinimalLocalWeakUpperGradient m φ D
    · exact (weakGradient_isMinimal h).1.1.aemeasurable
    · simp only [weakGradient,dite_eq_right h]
      exact aemeasurable_const
  rw [lintegral_map' ((hmeas.mono_ac hq).ennreal_ofReal.pow_const 2) measurable_fst.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [weakGradient_le_contact_distance hfinite hφ hdual hq hcontact] with z hz
  rw [edist_dist]
  exact pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal hz) 2

end WeakHessian

end
end InlinedFile0

end OAI
