import OAI.Probability.SLE.Geometry.ContinuousRangeCompletion

namespace OAI

/-! Transfer of Borel parameter families under a finite path law, with one
exceptional set for all parameters. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace SLEExactGauge

lemma nullMeasurableSet_forall_parameter
    {X T : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [MeasurableSpace T] [StandardBorelSpace T]
    (μ : Measure X) [IsFiniteMeasure μ] (p : T → X → Prop)
    (hp : MeasurableSet {q : T × X | p q.1 q.2}) :
    NullMeasurableSet {x | ∀ t, p t x} μ := by
  have hbad : AnalyticSet (Prod.snd '' {q : T × X | ¬p q.1 q.2}) :=
    hp.compl.analyticSet_image measurable_snd
  have heq : {x | ∀ t, p t x}=(Prod.snd '' {q : T × X | ¬p q.1 q.2})ᶜ := by
    ext x
    simp only [mem_compl_iff,mem_image,mem_ofPred_eq,Prod.exists,
      exists_eq_right,not_exists,not_not]
  rw [heq]
  exact (nullMeasurableSet_of_analytic_finite μ hbad).compl

lemma ae_map_iff_nullMeasurableSet
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} {f : Ω → X} (hf : AEMeasurable f P) {p : X → Prop}
    (hp : NullMeasurableSet {x | p x} (P.map f)) :
    (∀ᵐ x ∂P.map f, p x) ↔ ∀ᵐ ω ∂P, p (f ω) := by
  have hn : NullMeasurableSet {x | ¬p x} (P.map f) := hp.compl
  rw [ae_iff,Measure.map_apply₀ hf hn]
  rfl

lemma ae_forall_parameter_of_hasLaw
    {Ω X T : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [MeasurableSpace T] [StandardBorelSpace T]
    {P : Measure Ω} {μ : Measure X} [IsFiniteMeasure μ]
    {f : Ω → X} (hf : HasLaw f μ P) (p : T → X → Prop)
    (hp : MeasurableSet {q : T × X | p q.1 q.2})
    (h : ∀ᵐ ω ∂P, ∀ t, p t (f ω)) :
    ∀ᵐ x ∂μ, ∀ t, p t x := by
  have hn := nullMeasurableSet_forall_parameter μ p hp
  rw [← hf.map_eq] at hn ⊢
  exact (ae_map_iff_nullMeasurableSet hf.aemeasurable hn).mpr h

end SLEExactGauge

end

end OAI
