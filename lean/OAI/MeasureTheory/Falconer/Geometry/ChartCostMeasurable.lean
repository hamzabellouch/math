import OAI.MeasureTheory.Falconer.Slicing.GaussianChartPairAverage
import OAI.MeasureTheory.Falconer.Slicing.GaussianChartTripleAverage

namespace OAI

/-! # Measurable original pair and triple costs as functions of the Gaussian rows -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ}

lemma chart_pair_cost_measurable (μ : Measure (Space n)) [SFinite μ]
    (r : ℝ) (E : Set (Space n × Space n)) (hE : MeasurableSet E) :
    Measurable (fun A : Fin h → Space (n+1) =>
      ((gaussianChartSliceMeasure μ A r).prod (gaussianChartSliceMeasure μ A r)) E) := by
  let B : Set ((Fin h → Space (n+1)) × (Space n × Space n)) :=
    {p | p.2 ∈ E ∧ ∀ i, |inner ℝ (gnomonicChart p.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.2.2 : Space (n+1)) (p.1 i)| ≤ r}
  have hb : MeasurableSet B := by
    have hc : MeasurableSet {p : (Fin h → Space (n+1)) × (Space n × Space n) | ∀ i, |inner ℝ (gnomonicChart p.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
        |inner ℝ (gnomonicChart p.2.2 : Space (n+1)) (p.1 i)| ≤ r} := by
      simp only [ofPred_forall,ofPred_and]
      apply MeasurableSet.iInter
      intro i
      have h₁ : Measurable (fun p : (Fin h → Space (n+1)) × (Space n × Space n) =>
          (gnomonicChart p.2.1 : Space (n+1))) :=
        measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
      have h₂ : Measurable (fun p : (Fin h → Space (n+1)) × (Space n × Space n) =>
          (gnomonicChart p.2.2 : Space (n+1))) :=
        measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
      exact (measurableSet_le (by fun_prop) measurable_const).inter
        (measurableSet_le (by fun_prop) measurable_const)
    exact (hE.preimage measurable_snd).inter hc
  have hm := (measurable_measure_prodMk_left (ν := μ.prod μ) hb).const_mul
    ((ENNReal.ofReal (r^(-(h:ℝ))))^2)
  convert hm using 1
  ext A
  simp only [gaussianChartSliceMeasure,Measure.prod_smul_left,Measure.prod_smul_right,
    Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,Measure.restrict_apply hE,pow_two,mul_assoc]
  have hs : E ∩ ((gnomonicChart ⁻¹' gaussianDirectionBand A r) ×ˢ
      (gnomonicChart ⁻¹' gaussianDirectionBand A r)) = Prod.mk A ⁻¹' B := by
    ext w
    simp only [B,mem_preimage,mem_ofPred_eq,mem_inter_iff,mem_prod,gaussianDirectionBand,forall_and]
  rw [hs]

theorem chart_triple_cost_measurable (μ : Measure (Space n)) [SFinite μ]
    (r : ℝ) (E : Set (Space n × Space n × Space n)) (hE : MeasurableSet E) :
    Measurable (fun A : Fin h → Space (n+1) =>
      ((gaussianChartSliceMeasure μ A r).prod
        ((gaussianChartSliceMeasure μ A r).prod (gaussianChartSliceMeasure μ A r))) E) := by
  let B : Set ((Fin h → Space (n+1)) × (Space n × Space n × Space n)) :=
    {p | p.2 ∈ E ∧ ∀ i, |inner ℝ (gnomonicChart p.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.2.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.2.2.2 : Space (n+1)) (p.1 i)| ≤ r}
  have hb : MeasurableSet B := by
    have hc : MeasurableSet {p : (Fin h → Space (n+1)) × (Space n × Space n × Space n) | ∀ i, |inner ℝ (gnomonicChart p.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
        |inner ℝ (gnomonicChart p.2.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
        |inner ℝ (gnomonicChart p.2.2.2 : Space (n+1)) (p.1 i)| ≤ r} := by
      simp only [ofPred_forall,ofPred_and]
      apply MeasurableSet.iInter
      intro i
      have h₁ : Measurable (fun p : (Fin h → Space (n+1)) × (Space n × Space n × Space n) =>
          (gnomonicChart p.2.1 : Space (n+1))) :=
        measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
      have h₂ : Measurable (fun p : (Fin h → Space (n+1)) × (Space n × Space n × Space n) =>
          (gnomonicChart p.2.2.1 : Space (n+1))) :=
        measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
      have h₃ : Measurable (fun p : (Fin h → Space (n+1)) × (Space n × Space n × Space n) =>
          (gnomonicChart p.2.2.2 : Space (n+1))) :=
        measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
      exact (measurableSet_le (by fun_prop) measurable_const).inter
        ((measurableSet_le (by fun_prop) measurable_const).inter
          (measurableSet_le (by fun_prop) measurable_const))
    exact (hE.preimage measurable_snd).inter hc
  have hm := (measurable_measure_prodMk_left (ν := μ.prod (μ.prod μ)) hb).const_mul
    ((ENNReal.ofReal (r^(-(h:ℝ))))^3)
  convert hm using 1
  ext A
  rw [gaussian_chart_triple_identity μ A r E hE]
  have hs : E ∩ chartTripleBand A r = Prod.mk A ⁻¹' B := by
    ext w
    simp only [B,chartTripleBand,mem_preimage,mem_ofPred_eq,mem_inter_iff,mem_prod,
      gaussianDirectionBand,forall_and]
  rw [hs]

end Falconer

end OAI
