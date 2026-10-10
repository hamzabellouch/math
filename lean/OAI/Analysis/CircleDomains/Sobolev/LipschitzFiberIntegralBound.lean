import OAI.Analysis.CircleDomains.Selection.ShrinkingFiberCovers
import OAI.Analysis.CircleDomains.Selection.SmallHausdorffCovers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! The sharp one-dimensional coarea inequality from Hausdorff covers.
No rectifiability is needed. Closed images of the covers are measurable
majorants; Fatou's lemma passes their counting bounds to the fibers. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma lipschitz_fiber_integral_le
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) (hA : (μH[1] : Measure X) A < ∞)
    (L : ℝ≥0) (f : X → ℝ) (hf : LipschitzWith L f) :
    (∫⁻ y, (μH[0] : Measure X) (A ∩ f ⁻¹' {y})) ≤
      (L : ℝ≥0∞) * (μH[1] : Measure X) A := by
  let ε : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / (n + 1 : ℝ))
  have hε : ∀ n, 0 < ε n := fun n => ENNReal.ofReal_pos.mpr (by positivity)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose T hcover hdiam hcost using fun n =>
    exists_small_hausdorff_cover A hA (ε n) (ε n) (hε n) (hε n)
  let g : ℕ → ℝ → ℝ≥0∞ := fun n y =>
    ∑' k, if y ∈ closure (f '' T n k) then 1 else 0
  have hgm : ∀ n, Measurable (g n) := by
    intro n
    apply Measurable.tsum
    intro k
    exact Measurable.ite isClosed_closure.measurableSet measurable_const measurable_const
  have hgint : ∀ n, (∫⁻ y, g n y) ≤
      (L : ℝ≥0∞) * ((μH[1] : Measure X) A + ε n) := by
    intro n
    calc
      (∫⁻ y, g n y) = ∑' k, volume (closure (f '' T n k)) := by
        rw [show g n = fun y => ∑' k, (closure (f '' T n k)).indicator
          (fun _ => (1 : ℝ≥0∞)) y by rfl]
        rw [lintegral_tsum (fun k => measurable_const.indicator
          isClosed_closure.measurableSet |>.aemeasurable)]
        simp only [lintegral_indicator isClosed_closure.measurableSet, lintegral_one,
          Measure.restrict_apply_univ]
      _ ≤ ∑' k, (L : ℝ≥0∞) * ediam (T n k) := by
        apply ENNReal.tsum_le_tsum
        intro k
        exact (Real.volume_le_diam _).trans ((ediam_closure _).le.trans (hf.ediam_image_le _))
      _ = (L : ℝ≥0∞) * ∑' k, ediam (T n k) := ENNReal.tsum_mul_left
      _ ≤ (L : ℝ≥0∞) * ((μH[1] : Measure X) A + ε n) := by
        gcongr
        exact (hcost n).le
  have hb : (∫⁻ y, (μH[0] : Measure X) (A ∩ f ⁻¹' {y})) ≤
      liminf (fun n => ∫⁻ y, g n y) atTop :=
    (lintegral_mono (hausdorff_zero_fiber_le_liminf_cover A f ε hεlim T hdiam hcover)).trans
      (lintegral_liminf_le hgm)
  apply hb.trans
  have ht : Tendsto (fun n => (L : ℝ≥0∞) * ((μH[1] : Measure X) A + ε n)) atTop
      (𝓝 ((L : ℝ≥0∞) * (μH[1] : Measure X) A)) := by
    simpa only [add_zero] using
      ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hεlim) (Or.inr ENNReal.coe_ne_top)
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (.of_forall hgint)

end CircleDomainRigidity

end

end OAI
