import OAI.Analysis.RCDHeat.TestPlanContinuous

namespace OAI

/-! # A local spatial full-measure property along compressed geodesics -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem testPlan_eval_property_on (μ : Measure X) (π : Measure C(Time,X))
    [IsFiniteMeasure π] {C : ℝ≥0∞}
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    {Ω : Set X} (hΩ : MeasurableSet Ω)
    (hstay : ∀ᵐ γ ∂π, ∀ t : Time, γ t∈Ω) {P : X → Prop}
    (hP : ∀ᵐ x ∂μ.restrict Ω, P x) :
    ∀ᵐ γ ∂π, ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), P (geodesicExtension γ t) := by
  have hc := (ae_restrict_iff' hΩ).mp hP
  have hac := Measure.absolutelyContinuous_of_le_smul (testPlanMeasure_compression μ π hcomp)
  have hh := ae_of_ae_map testPlanEval_measurable.aemeasurable (hc.filter_mono hac.ae_le)
  have ht := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hh)
  filter_upwards [ht,hstay] with γ hγ hs
  filter_upwards [hγ] with t hp
  apply hp
  exact hs (Set.projIcc 0 1 zero_le_one t)

end RegularPointCoordinates

end

end OAI
