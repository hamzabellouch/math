import OAI.MeasureTheory.Falconer.Angular.GnomonicPrunedLaw
import OAI.MeasureTheory.Falconer.Geometry.SelectTransverseChartTriple

namespace OAI

/-! # Transfer the original radial costs to a restricted chart slice -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {X : Type*} [MeasurableSpace X]

theorem restricted_chart_exceptional_triples
    (ν₀ : Measure (Space n)) [IsFiniteMeasure ν₀]
    (A : Fin h → Space (n+1)) (δ : ℝ) (D : Set (Space n))
    (G : Set (Space n × Space n)) (W : ℝ)
    {M P T : ℝ≥0∞}
    (hmass : ((gaussianChartSliceMeasure ν₀ A δ).restrict D) univ ≤ M)
    (hpair : ((gaussianChartSliceMeasure ν₀ A δ).prod
      (gaussianChartSliceMeasure ν₀ A δ)) Gᶜ ≤ P)
    (htriple : ((gaussianChartSliceMeasure ν₀ A δ).prod
      ((gaussianChartSliceMeasure ν₀ A δ).prod (gaussianChartSliceMeasure ν₀ A δ)))
      (badChartTriples G W) ≤ T) :
    let β := (gaussianChartSliceMeasure ν₀ A δ).restrict D
    (β.prod (β.prod β)) (badChartTriples G W)+2*β univ*(β.prod β) Gᶜ ≤ T+2*M*P := by
  intro β
  have hβ : β ≤ gaussianChartSliceMeasure ν₀ A δ := Measure.restrict_le_self
  have hp : (β.prod β) Gᶜ ≤ P := (Measure.prod_mono hβ hβ _).trans hpair
  have ht : (β.prod (β.prod β)) (badChartTriples G W) ≤ T :=
    (Measure.prod_mono hβ (Measure.prod_mono hβ hβ) _).trans htriple
  exact add_le_add ht (mul_le_mul' (mul_le_mul' le_rfl hmass) hp)

theorem exists_transverse_restricted_chart_triple
    (α : Measure X) (ν₀ : Measure (Space n)) [IsFiniteMeasure α] [IsFiniteMeasure ν₀]
    (A : Fin h → Space (n+1)) (δ : ℝ) (D : Set (Space n))
    (E : Set (X × Space n)) (hE : MeasurableSet E)
    (hbounded : ∀ u ∈ E, ‖u.2‖ ≤ 1)
    (G : Set (Space n × Space n)) (hG : MeasurableSet G) (W : ℝ)
    {M a : ℝ} {P T : ℝ≥0∞} (hM : 0 < M) (ha : 0 < a)
    (hα : α univ ≤ ENNReal.ofReal M)
    (hβ : ((gaussianChartSliceMeasure ν₀ A δ).restrict D) univ ≤ ENNReal.ofReal M)
    (hI : ENNReal.ofReal a ≤ (α.prod ((gaussianChartSliceMeasure ν₀ A δ).restrict D)) E)
    (hpair : ((gaussianChartSliceMeasure ν₀ A δ).prod
      (gaussianChartSliceMeasure ν₀ A δ)) Gᶜ ≤ P)
    (htriple : ((gaussianChartSliceMeasure ν₀ A δ).prod
      ((gaussianChartSliceMeasure ν₀ A δ).prod (gaussianChartSliceMeasure ν₀ A δ)))
      (badChartTriples G W) ≤ T)
    (hbudget : T+2*ENNReal.ofReal M*P ≤ ENNReal.ofReal (a^3/(4*M^3))) :
    ∃ w : Space n × Space n × Space n, W ≤ chartTripleVolume w ∧
      (w.1,w.2.1) ∈ G ∧ (w.1,w.2.2) ∈ G ∧
      ENNReal.ofReal (a^3/(2*M^5)) < α {x | (x,w) ∈ commonTripleRelation E} := by
  have hcost := restricted_chart_exceptional_triples ν₀ A δ D G W hβ hpair htriple
  exact exists_transverse_common_chart_triple α _ E hE hbounded G hG W hM ha hα hβ hI
    (hcost.trans hbudget)

end Falconer

end OAI
