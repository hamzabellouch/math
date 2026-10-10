import OAI.MeasureTheory.Falconer.Geometry.ChartCostMeasurable
import OAI.MeasureTheory.Falconer.Estimates.BadTripleRelation

namespace OAI

/-! # The two concrete radial costs used in endpoint slice selection -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ}

noncomputable def endpointPairCost (ν : Measure (Space n)) (δ : ℝ)
    (G : Set (Space n × Space n)) (A : Fin h → Space (n+1)) : ℝ≥0∞ :=
  ((gaussianChartSliceMeasure ν A δ).prod (gaussianChartSliceMeasure ν A δ)) Gᶜ

noncomputable def endpointTripleCost (ν : Measure (Space n)) (δ W : ℝ)
    (G : Set (Space n × Space n)) (A : Fin h → Space (n+1)) : ℝ≥0∞ :=
  ((gaussianChartSliceMeasure ν A δ).prod
    ((gaussianChartSliceMeasure ν A δ).prod (gaussianChartSliceMeasure ν A δ)))
    (badChartTriples G W)

theorem endpointPairCost_measurable (ν : Measure (Space n)) [SFinite ν] (δ : ℝ)
    {G : Set (Space n × Space n)} (hG : MeasurableSet G) :
    Measurable (endpointPairCost (h := h) ν δ G) := chart_pair_cost_measurable ν δ Gᶜ hG.compl

theorem endpointTripleCost_measurable (ν : Measure (Space n)) [SFinite ν] (δ W : ℝ)
    {G : Set (Space n × Space n)} (hG : MeasurableSet G) :
    Measurable (endpointTripleCost (h := h) ν δ W G) :=
  chart_triple_cost_measurable ν δ (badChartTriples G W) (badChartTriples_measurable hG W)

end Falconer

end OAI
