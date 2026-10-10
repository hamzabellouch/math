import OAI.MeasureTheory.Falconer.Slicing.GaussianPointBand
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-! # Active original tube-anchor counts in the Gaussian point parameter -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

noncomputable def gaussianActiveAnchorCount (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) (r : ℝ) (z : Space h) : ℕ := by
  classical
  exact (S.filter (fun i => a i ∈ gaussianPointBand A z r)).card

theorem gaussianActiveAnchorCount_eq_sum (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) (r : ℝ) (z : Space h) :
    (gaussianActiveAnchorCount A S a r z : ℝ≥0∞) =
      ∑ i ∈ S, {v : Space h | a i ∈ gaussianPointBand A v r}.indicator (fun _ => (1:ℝ≥0∞)) z := by
  classical
  simp only [gaussianActiveAnchorCount,Finset.natCast_card_filter,Set.indicator_apply,mem_ofPred_eq]

theorem measurable_gaussianActiveAnchorCount (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) (r : ℝ) :
    Measurable (fun z : Space h => (gaussianActiveAnchorCount A S a r z : ℝ≥0∞)) := by
  simp_rw [gaussianActiveAnchorCount_eq_sum]
  apply Finset.measurable_sum
  intro i _
  apply measurable_const.indicator
  change MeasurableSet {v : Space h | ∀ j, |inner ℝ (a i) (A j)-v j| ≤ r}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)

theorem gaussianActiveAnchorCount_integral (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ z : Space h, (gaussianActiveAnchorCount A S a r z : ℝ≥0∞)) =
      (S.card:ℝ≥0∞)*ENNReal.ofReal ((2*r)^h) := by
  simp_rw [gaussianActiveAnchorCount_eq_sum]
  have hm (i : ι) : MeasurableSet {v : Space h | a i ∈ gaussianPointBand A v r} := by
    change MeasurableSet {v : Space h | ∀ j, |inner ℝ (a i) (A j)-v j| ≤ r}
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  rw [lintegral_finsetSum S (fun i _ => measurable_const.indicator (hm i))]
  simp only [lintegral_indicator_const (hm _),one_mul,gaussianPointBand_parameter_measure A _ hr,
    Finset.sum_const,nsmul_eq_mul]

theorem gaussianActiveAnchorCount_exceptional (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) {r : ℝ} (hr : 0 ≤ r)
    {T : ℝ≥0∞} (hT : T ≠ 0) (hTfin : T ≠ ∞) :
    volume {z : Space h | T < (gaussianActiveAnchorCount A S a r z : ℝ≥0∞)} ≤
      ((S.card:ℝ≥0∞)*ENNReal.ofReal ((2*r)^h))/T := by
  apply (measure_mono (show {z : Space h | T < (gaussianActiveAnchorCount A S a r z : ℝ≥0∞)} ⊆
      {z : Space h | T ≤ (gaussianActiveAnchorCount A S a r z : ℝ≥0∞)} from
    fun _ hz => (show T < _ from hz).le)).trans
  rw [← gaussianActiveAnchorCount_integral A S a hr]
  exact meas_ge_le_lintegral_div (measurable_gaussianActiveAnchorCount A S a r).aemeasurable hT hTfin

end Falconer

end OAI
