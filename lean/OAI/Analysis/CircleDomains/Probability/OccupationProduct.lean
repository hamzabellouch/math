import OAI.Analysis.CircleDomains.Probability.CodeLawMeasures
import Mathlib.MeasureTheory.Measure.FiniteMeasure

namespace OAI

/-! Independence commutes with taking the mean physical occupation measure.
This identifies the expected two-path kernel integral with its density integral. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem measurable_finite_measure_product
    {A B X Y : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : A → Measure X) (ν : B → Measure Y)
    [∀ a, IsFiniteMeasure (μ a)] [∀ b, IsFiniteMeasure (ν b)]
    (hμ : Measurable μ) (hν : Measurable ν) :
    Measurable (fun p : A × B => (μ p.1).prod (ν p.2)) := by
  let mf : A → FiniteMeasure X := fun a => ⟨μ a, inferInstance⟩
  let nf : B → FiniteMeasure Y := fun b => ⟨ν b, inferInstance⟩
  have hm : Measurable mf := hμ.subtype_mk
  have hn : Measurable nf := hν.subtype_mk
  exact FiniteMeasure.measurable_fun_prod.comp
    ((hm.comp measurable_fst).prodMk (hn.comp measurable_snd))

theorem product_bind_finite_measures
    {A B X Y : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure A) (Q : Measure B) [SFinite P] [SFinite Q]
    (μ : A → Measure X) (ν : B → Measure Y)
    [∀ a, IsFiniteMeasure (μ a)] [∀ b, IsFiniteMeasure (ν b)]
    [SigmaFinite (P.bind μ)] [SigmaFinite (Q.bind ν)]
    (hμ : Measurable μ) (hν : Measurable ν) :
    (P.bind μ).prod (Q.bind ν) =
      (P.prod Q).bind (fun p => (μ p.1).prod (ν p.2)) := by
  apply Measure.prod_eq
  intro s t hs ht
  rw [Measure.bind_apply (hs.prod ht)
    (measurable_finite_measure_product μ ν hμ hν).aemeasurable]
  simp_rw [Measure.prod_prod]
  rw [lintegral_prod_mul
    (show Measurable (fun a => μ a s) from (Measure.measurable_coe hs).comp hμ).aemeasurable
    (show Measurable (fun b => ν b t) from (Measure.measurable_coe ht).comp hν).aemeasurable,
    Measure.bind_apply hs hμ.aemeasurable, Measure.bind_apply ht hν.aemeasurable]

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)]
  [BorelSpace C(PathTime, Y)]

theorem mean_code_pair_occupation (d e : PathCodeData X Y)
    (hd : IsOpen d.quotientDomain) (he : IsOpen e.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    [SigmaFinite (meanCodeOccupation d P)] [SigmaFinite (meanCodeOccupation e Q)]
    (K : Y × Y → ℝ≥0∞) (hK : Measurable K) :
    (∫⁻ p, ∫⁻ z, K z ∂(baseCodeOccupation d p.1).prod (baseCodeOccupation e p.2)
      ∂(P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))) =
      ∫⁻ z, K z ∂(meanCodeOccupation d P).prod (meanCodeOccupation e Q) := by
  have hm := measurable_baseCodeOccupation d hd
  have hn := measurable_baseCodeOccupation e he
  let : SigmaFinite ((P : Measure (BasePathCode d)).bind (baseCodeOccupation d)) :=
    inferInstanceAs (SigmaFinite (meanCodeOccupation d P))
  let : SigmaFinite ((Q : Measure (BasePathCode e)).bind (baseCodeOccupation e)) :=
    inferInstanceAs (SigmaFinite (meanCodeOccupation e Q))
  rw [meanCodeOccupation, meanCodeOccupation,
    product_bind_finite_measures (P : Measure (BasePathCode d)) (Q : Measure (BasePathCode e))
      (baseCodeOccupation d) (baseCodeOccupation e) hm hn,
    Measure.lintegral_bind (measurable_finite_measure_product _ _ hm hn).aemeasurable
      hK.aemeasurable]

end CircleDomainRigidity

end

end OAI
