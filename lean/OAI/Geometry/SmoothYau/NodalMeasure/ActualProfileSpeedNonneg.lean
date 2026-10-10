import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.GlobalPrepDualNorm

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace YauCounterexamples
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma actualProfileSpeed_nonneg (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    0 ≤ actualProfileSpeed g u x := actualCoordinateNorm_nonneg g x _

lemma integrableOn_actualProfileSpeed (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) {Ω : Set E} (hΩ : IsCompact (closure Ω))
    (μ : Measure E) [IsLocallyFiniteMeasure μ] : IntegrableOn (actualProfileSpeed g u) Ω μ :=
  ((continuous_actualProfileSpeed g hu).continuousOn.integrableOn_compact hΩ).mono_set subset_closure

def actualProfileMass (g : SmoothMetric E E) (u : E → ℝ) (μ : Measure E) (Ω : Set E) : ℝ :=
  ∫ x in Ω, actualProfileSpeed g u x ∂μ

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma actualProfileMass_nonneg (g : SmoothMetric E E) (u : E → ℝ) (μ : Measure E) (Ω : Set E) :
    0 ≤ actualProfileMass g u μ Ω := integral_nonneg (actualProfileSpeed_nonneg g u)

def actualProfileWeightedMeasure (g : SmoothMetric E E) (u : E → ℝ) (μ : Measure E) (Ω : Set E) : Measure E :=
  (μ.restrict Ω).withDensity (fun x => ENNReal.ofReal (actualProfileSpeed g u x))

lemma actualProfileWeightedMeasure_finite (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) {Ω : Set E} (hΩ : IsCompact (closure Ω))
    (μ : Measure E) [IsLocallyFiniteMeasure μ] :
    IsFiniteMeasure (actualProfileWeightedMeasure g u μ Ω) :=
  isFiniteMeasure_withDensity_ofReal (integrableOn_actualProfileSpeed g hu hΩ μ).2

lemma actualProfileWeightedMeasure_apply (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) {Ω : Set E} (hΩ : IsCompact (closure Ω))
    (μ : Measure E) [IsLocallyFiniteMeasure μ] {S : Set E} (hS : MeasurableSet S) :
    actualProfileWeightedMeasure g u μ Ω S =
      ENNReal.ofReal (∫ x in S, actualProfileSpeed g u x ∂(μ.restrict Ω)) := by
  rw [actualProfileWeightedMeasure,withDensity_apply _ hS]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrableOn_actualProfileSpeed g hu hΩ μ).integrableOn
    (ae_of_all _ (actualProfileSpeed_nonneg g u))).symm

lemma actualProfileWeightedMeasure_self (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) {Ω : Set E} (hΩ : IsCompact (closure Ω)) (hΩm : MeasurableSet Ω)
    (μ : Measure E) [IsLocallyFiniteMeasure μ] :
    actualProfileWeightedMeasure g u μ Ω Ω = ENNReal.ofReal (actualProfileMass g u μ Ω) := by
  rw [actualProfileWeightedMeasure_apply g hu hΩ μ hΩm,Measure.restrict_restrict hΩm,
    inter_self,actualProfileMass]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma actualProfileSpeed_relative_error (g : SmoothMetric E E) (u v : E → ℝ) (x : E)
    {ε : ℝ} (h : actualCoordinateNorm g x
      (coordinateMetricGradient g v x-coordinateMetricGradient g u x) ≤ ε*actualProfileSpeed g u x) :
    (1-ε)*actualProfileSpeed g u x ≤ actualProfileSpeed g v x ∧
      actualProfileSpeed g v x ≤ (1+ε)*actualProfileSpeed g u x := by
  have hh := (actualCoordinateNorm_abs_sub g x
    (coordinateMetricGradient g v x) (coordinateMetricGradient g u x)).trans h
  change |actualProfileSpeed g v x-actualProfileSpeed g u x| ≤ ε*actualProfileSpeed g u x at hh
  obtain ⟨hl,hr⟩ := abs_le.mp hh
  constructor <;> linarith

end YauCounterexamples

end

end OAI
