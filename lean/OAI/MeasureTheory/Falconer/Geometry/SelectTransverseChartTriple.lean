import OAI.MeasureTheory.Falconer.Estimates.AnchoredPairFailure
import OAI.MeasureTheory.Falconer.Estimates.SelectBoundedCommonTriple

namespace OAI

/-! # A transverse triple with common incidence in the original chart labels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] {n : ℕ}

theorem exists_transverse_common_chart_triple
    (μ : Measure X) (ν : Measure (Space n)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (X × Space n)) (hE : MeasurableSet E)
    (hbounded : ∀ u ∈ E, ‖u.2‖ ≤ 1)
    (G : Set (Space n × Space n)) (hG : MeasurableSet G) (W : ℝ)
    {M a : ℝ} (hM : 0 < M) (ha : 0 < a)
    (hμ : μ univ ≤ ENNReal.ofReal M) (hν : ν univ ≤ ENNReal.ofReal M)
    (hI : ENNReal.ofReal a ≤ (μ.prod ν) E)
    (hbad : (ν.prod (ν.prod ν)) (badChartTriples G W)+
      2*ν univ*(ν.prod ν) Gᶜ ≤ ENNReal.ofReal (a^3/(4*M^3))) :
    ∃ w : Space n × Space n × Space n, W ≤ chartTripleVolume w ∧
      (w.1,w.2.1) ∈ G ∧ (w.1,w.2.2) ∈ G ∧
      ENNReal.ofReal (a^3/(2*M^5)) < μ {x | (x,w) ∈ commonTripleRelation E} := by
  obtain ⟨w,hw,hcommon⟩ := exists_good_common_triple_bounded μ ν E hE
    (endpointExceptionalTriples G W) (endpointExceptionalTriples_measurable hG W)
    hM ha hμ hν hI ((endpointExceptionalTriples_mass ν hG W).trans hbad)
  have hn : {x | (x,w) ∈ commonTripleRelation E}.Nonempty := by
    by_contra h
    have he : {x | (x,w) ∈ commonTripleRelation E} = ∅ := not_nonempty_iff_eq_empty.mp h
    rw [he,measure_empty] at hcommon
    exact (not_lt_of_ge (bot_le : (0 : ℝ≥0∞) ≤ _)) hcommon
  obtain ⟨x,hx⟩ := hn
  change (x,w.1) ∈ E ∧ (x,w.2.1) ∈ E ∧ (x,w.2.2) ∈ E at hx
  have hw₁ : ‖w.1‖ ≤ 1 := hbounded (x,w.1) hx.1
  have hw₂ : ‖w.2.1‖ ≤ 1 := hbounded (x,w.2.1) hx.2.1
  have hw₃ : ‖w.2.2‖ ≤ 1 := hbounded (x,w.2.2) hx.2.2
  have hvol : W ≤ chartTripleVolume w := endpointExceptionalTriples_volume hw hw₁ hw₂ hw₃
  refine ⟨w,hvol,?_,?_,hcommon⟩
  · by_contra hp
    apply hw
    change w ∈ badChartTriples G W ∨ (w.1,w.2.1) ∈ Gᶜ ∨ (w.1,w.2.2) ∈ Gᶜ
    exact Or.inr (Or.inl hp)
  · by_contra hp
    apply hw
    change w ∈ badChartTriples G W ∨ (w.1,w.2.1) ∈ Gᶜ ∨ (w.1,w.2.2) ∈ Gᶜ
    exact Or.inr (Or.inr hp)

end Falconer

end OAI
