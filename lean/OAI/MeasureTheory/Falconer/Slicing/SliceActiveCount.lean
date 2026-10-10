import OAI.MeasureTheory.Falconer.Slicing.SliceMass
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-! # Actual active-anchor counts in point slices -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

noncomputable def activeSliceAnchorCount (V : Submodule ℝ (Space d))
    (S : Finset ι) (a : ι → Space d) (δ : ℝ) (z : Vᗮ) : ℕ := by
  classical
  exact (S.filter (fun i => a i ∈ pointSliceBand V z δ)).card

theorem activeSliceAnchorCount_eq_sum (V : Submodule ℝ (Space d))
    (S : Finset ι) (a : ι → Space d) (δ : ℝ) (z : Vᗮ) :
    (activeSliceAnchorCount V S a δ z : ℝ≥0∞) =
      ∑ i ∈ S, {u : Vᗮ | a i ∈ pointSliceBand V u δ}.indicator (fun _ => (1:ℝ≥0∞)) z := by
  classical
  simp only [activeSliceAnchorCount,Finset.natCast_card_filter,Set.indicator_apply,mem_ofPred_eq]

theorem measurable_activeSliceAnchorCount (V : Submodule ℝ (Space d))
    (S : Finset ι) (a : ι → Space d) (δ : ℝ) :
    Measurable (fun z : Vᗮ => (activeSliceAnchorCount V S a δ z : ℝ≥0∞)) := by
  simp_rw [activeSliceAnchorCount_eq_sum]
  apply Finset.measurable_sum
  intro i _
  apply measurable_const.indicator
  exact measurableSet_le
    (show Measurable (fun u : Vᗮ => ‖Vᗮ.starProjection (a i)-(u:Space d)‖) from by fun_prop)
    measurable_const

theorem activeSliceAnchorCount_integral (V : Submodule ℝ (Space d))
    (S : Finset ι) (a : ι → Space d) (δ : ℝ) :
    (∫⁻ z : Vᗮ, (activeSliceAnchorCount V S a δ z : ℝ≥0∞)) =
      (S.card:ℝ≥0∞)*(volume : Measure Vᗮ) (closedBall 0 δ) := by
  simp_rw [activeSliceAnchorCount_eq_sum]
  have hm (i : ι) : MeasurableSet {u : Vᗮ | a i ∈ pointSliceBand V u δ} := by
    exact measurableSet_le
      (show Measurable (fun u : Vᗮ => ‖Vᗮ.starProjection (a i)-(u:Space d)‖) from by fun_prop)
      measurable_const
  rw [lintegral_finsetSum S (fun i _ => measurable_const.indicator (hm i))]
  simp only [lintegral_indicator_const (hm _),one_mul,pointSliceBand_parameter_measure,
    Finset.sum_const, nsmul_eq_mul]

theorem activeSliceAnchorCount_exceptional (V : Submodule ℝ (Space d))
    (S : Finset ι) (a : ι → Space d) (δ : ℝ) {T : ℝ≥0∞}
    (hT : T ≠ 0) (hTfin : T ≠ ∞) :
    (volume : Measure Vᗮ) {z | T < (activeSliceAnchorCount V S a δ z : ℝ≥0∞)} ≤
      ((S.card:ℝ≥0∞)*(volume : Measure Vᗮ) (closedBall 0 δ))/T := by
  have hsub : {z : Vᗮ | T < (activeSliceAnchorCount V S a δ z : ℝ≥0∞)} ⊆
      {z : Vᗮ | T ≤ (activeSliceAnchorCount V S a δ z : ℝ≥0∞)} := by
    intro z hz
    exact (show T < (activeSliceAnchorCount V S a δ z : ℝ≥0∞) from hz).le
  apply (measure_mono hsub).trans
  rw [← activeSliceAnchorCount_integral V S a δ]
  exact meas_ge_le_lintegral_div (measurable_activeSliceAnchorCount V S a δ).aemeasurable hT hTfin

end Falconer

end OAI
