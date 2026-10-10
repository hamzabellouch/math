import OAI.MeasureTheory.Falconer.Slicing.GaussianChartTripleAverage

namespace OAI

/-! # Joint measurability of the actual chart triple kernel -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem gaussianChartTripleWeight_measurable (r : ℝ) :
    Measurable (fun w : Space n × Space n × Space n => gaussianChartTripleWeight h r w.1 w.2.1 w.2.2) := by
  let S : Set ((Space n × Space n × Space n) × (Fin h → Space (n+1))) :=
    {p | ∀ i, |inner ℝ (gnomonicChart p.1.1 : Space (n+1)) (p.2 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.1.2.1 : Space (n+1)) (p.2 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.1.2.2 : Space (n+1)) (p.2 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall,ofPred_and]
    apply MeasurableSet.iInter
    intro i
    have h₁ : Measurable (fun p : (Space n × Space n × Space n) × (Fin h → Space (n+1)) =>
        (gnomonicChart p.1.1 : Space (n+1))) :=
      measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
    have h₂ : Measurable (fun p : (Space n × Space n × Space n) × (Fin h → Space (n+1)) =>
        (gnomonicChart p.1.2.1 : Space (n+1))) :=
      measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
    have h₃ : Measurable (fun p : (Space n × Space n × Space n) × (Fin h → Space (n+1)) =>
        (gnomonicChart p.1.2.2 : Space (n+1))) :=
      measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      ((measurableSet_le (by fun_prop) measurable_const).inter
        (measurableSet_le (by fun_prop) measurable_const))
  exact (measurable_measure_prodMk_left (ν := gaussianRows (n+1) h) hS).const_mul _

end Falconer

end OAI
