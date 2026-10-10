import OAI.MeasureTheory.Falconer.Slicing.GnomonicSliceLaw
import OAI.MeasureTheory.Falconer.Slicing.GaussianSliceMass

namespace OAI

/-! # Exact pair averaging on the original chart labels -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

noncomputable def gaussianChartPairWeight (h : ℕ) (r : ℝ) (p q : Space n) : ℝ≥0∞ :=
  (ENNReal.ofReal (r^(-(h:ℝ))))^2 * gaussianRows (n+1) h
    {A | ∀ i, |inner ℝ (gnomonicChart p : Space (n+1)) (A i)| ≤ r ∧
      |inner ℝ (gnomonicChart q : Space (n+1)) (A i)| ≤ r}

theorem gaussian_chart_pair_average (μ : Measure (Space n)) [SFinite μ]
    (r : ℝ) (E : Set (Space n × Space n)) (hE : MeasurableSet E) :
    (∫⁻ A : Fin h → Space (n+1), ((gaussianChartSliceMeasure μ A r).prod
      (gaussianChartSliceMeasure μ A r)) E ∂gaussianRows (n+1) h) =
      ∫⁻ w in E, gaussianChartPairWeight h r w.1 w.2 ∂μ.prod μ := by
  let D : (Fin h → Space (n+1)) → Set (Space n) :=
    fun A => gnomonicChart ⁻¹' gaussianDirectionBand A r
  have hD (A : Fin h → Space (n+1)) : MeasurableSet (D A) :=
    (gaussianDirectionBand_measurable A r).preimage (gnomonicChart_continuous n).measurable
  have he (A : Fin h → Space (n+1)) :
      ((gaussianChartSliceMeasure μ A r).prod (gaussianChartSliceMeasure μ A r)) E =
        (ENNReal.ofReal (r^(-(h:ℝ))))^2*(μ.prod μ) (E ∩ (D A ×ˢ D A)) := by
    simp only [gaussianChartSliceMeasure,Measure.prod_smul_left,Measure.prod_smul_right,
      Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,Measure.restrict_apply hE,D,pow_two,mul_assoc]
  simp_rw [he]
  have hc : (ENNReal.ofReal (r^(-(h:ℝ))))^2 ≠ ∞ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [lintegral_const_mul' _ _ hc]
  unfold gaussianChartPairWeight
  rw [lintegral_const_mul' _ _ hc]
  congr 1
  let S : Set ((Fin h → Space (n+1)) × (Space n × Space n)) :=
    {p | ∀ i, |inner ℝ (gnomonicChart p.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.2.2 : Space (n+1)) (p.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall,ofPred_and]
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
  have hs (A : Fin h → Space (n+1)) : Prod.mk A ⁻¹' S = D A ×ˢ D A := by
    ext w
    simp only [S,D,gaussianDirectionBand,mem_preimage,mem_ofPred_eq,mem_prod,forall_and]
  calc
    _ = ∫⁻ A : Fin h → Space (n+1), ((μ.prod μ).restrict E) (Prod.mk A ⁻¹' S)
        ∂gaussianRows (n+1) h := by
      apply lintegral_congr
      intro A
      rw [hs,Measure.restrict_apply ((hD A).prod (hD A)),inter_comm]
    _ = ((gaussianRows (n+1) h).prod ((μ.prod μ).restrict E)) S := (Measure.prod_apply hS).symm
    _ = _ := Measure.prod_apply_symm hS

end Falconer

end OAI
