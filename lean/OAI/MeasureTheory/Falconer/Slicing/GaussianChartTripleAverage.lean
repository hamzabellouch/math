import OAI.MeasureTheory.Falconer.Slicing.GnomonicSliceLaw
import OAI.MeasureTheory.Falconer.Recursion.AnchoredTriplePotential

namespace OAI

/-! # Exact Gaussian averaging on triples of the original affine chart labels -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

def chartTripleBand (A : Fin h → Space (n+1)) (r : ℝ) :
    Set (Space n × Space n × Space n) :=
  (gnomonicChart ⁻¹' gaussianDirectionBand A r) ×ˢ
    ((gnomonicChart ⁻¹' gaussianDirectionBand A r) ×ˢ
      (gnomonicChart ⁻¹' gaussianDirectionBand A r))

theorem chartTripleBand_measurable (A : Fin h → Space (n+1)) (r : ℝ) :
    MeasurableSet (chartTripleBand A r) := by
  have hm := (gaussianDirectionBand_measurable A r).preimage (gnomonicChart_continuous n).measurable
  exact hm.prod (hm.prod hm)

theorem gaussian_chart_triple_identity (μ : Measure (Space n)) [SFinite μ]
    (A : Fin h → Space (n+1)) (r : ℝ) (E : Set (Space n × Space n × Space n))
    (hE : MeasurableSet E) :
    ((gaussianChartSliceMeasure μ A r).prod
      ((gaussianChartSliceMeasure μ A r).prod (gaussianChartSliceMeasure μ A r))) E =
      (ENNReal.ofReal (r^(-(h:ℝ))))^3*(μ.prod (μ.prod μ)) (E ∩ chartTripleBand A r) := by
  simp only [gaussianChartSliceMeasure,Measure.prod_smul_left,Measure.prod_smul_right,
    Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,Measure.restrict_apply hE,
    chartTripleBand,pow_succ,pow_zero,one_mul,mul_assoc]

theorem gaussian_chart_triple_average (μ : Measure (Space n)) [SFinite μ]
    (r : ℝ) (E : Set (Space n × Space n × Space n)) (hE : MeasurableSet E) :
    (∫⁻ A : Fin h → Space (n+1), ((gaussianChartSliceMeasure μ A r).prod
      ((gaussianChartSliceMeasure μ A r).prod (gaussianChartSliceMeasure μ A r))) E
        ∂gaussianRows (n+1) h) =
      ∫⁻ w in E, gaussianChartTripleWeight h r w.1 w.2.1 w.2.2 ∂μ.prod (μ.prod μ) := by
  simp_rw [gaussian_chart_triple_identity μ _ r E hE]
  have hc : (ENNReal.ofReal (r^(-(h:ℝ))))^3 ≠ ∞ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [lintegral_const_mul' _ _ hc]
  symm
  unfold gaussianChartTripleWeight
  rw [lintegral_const_mul' _ _ hc]
  congr 1
  let S : Set ((Fin h → Space (n+1)) × (Space n × Space n × Space n)) :=
    {p | ∀ i, |inner ℝ (gnomonicChart p.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.2.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.2.2.2 : Space (n+1)) (p.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall,ofPred_and]
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
  have hs (A : Fin h → Space (n+1)) : Prod.mk A ⁻¹' S = chartTripleBand A r := by
    ext w
    simp only [S,chartTripleBand,gaussianDirectionBand,mem_preimage,mem_ofPred_eq,mem_prod,forall_and]
  calc
    _ = ((gaussianRows (n+1) h).prod ((μ.prod (μ.prod μ)).restrict E)) S :=
      (Measure.prod_apply_symm hS).symm
    _ = ∫⁻ A : Fin h → Space (n+1), ((μ.prod (μ.prod μ)).restrict E) (Prod.mk A ⁻¹' S)
        ∂gaussianRows (n+1) h := Measure.prod_apply hS
    _ = _ := by
      apply lintegral_congr
      intro A
      rw [hs,Measure.restrict_apply (chartTripleBand_measurable A r),inter_comm]

end Falconer

end OAI
