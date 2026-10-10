import OAI.Analysis.CircleDomains.Modulus.ShrinkingLengthFibers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

namespace OAI

/-! A measurable majorant for the lengths of Lipschitz scalar fibers.
Only a finite two-dimensional Hausdorff measure is needed. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma exists_lipschitz_length_fiber_majorant
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) (hA : (μH[2] : Measure X) A < ∞)
    (L : ℝ≥0) (f : X → ℝ) (hf : LipschitzWith L f)
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
      (∀ y, (μH[1] : Measure X) (A ∩ f ⁻¹' {y}) ≤ G y) ∧
      (∫⁻ y, G y) ≤ (L : ℝ≥0∞) * ((μH[2] : Measure X) A + δ) := by
  let ε : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / (n + 1 : ℝ))
  have hε : ∀ n, 0 < ε n := fun n => ENNReal.ofReal_pos.mpr (by positivity)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose T hcover hdiam hcost using fun n =>
    exists_small_quadratic_hausdorff_cover A hA (ε n) δ (hε n) hδ
  let g : ℕ → ℝ → ℝ≥0∞ := fun n y =>
    ∑' k, if y ∈ closure (f '' T n k) then ediam (T n k) else 0
  have hgm : ∀ n, Measurable (g n) := by
    intro n
    apply Measurable.tsum
    intro k
    exact Measurable.ite isClosed_closure.measurableSet measurable_const measurable_const
  have hgint : ∀ n, (∫⁻ y, g n y) ≤ (L : ℝ≥0∞) * ((μH[2] : Measure X) A + δ) := by
    intro n
    calc
      (∫⁻ y, g n y) = ∑' k, ediam (T n k) * volume (closure (f '' T n k)) := by
        rw [show g n = fun y => ∑' k, (closure (f '' T n k)).indicator
          (fun _ => ediam (T n k)) y by rfl]
        rw [lintegral_tsum (fun k => measurable_const.indicator
          isClosed_closure.measurableSet |>.aemeasurable)]
        simp only [lintegral_indicator isClosed_closure.measurableSet, lintegral_const,
          Measure.restrict_apply_univ]
      _ ≤ ∑' k, ediam (T n k) * ((L : ℝ≥0∞) * ediam (T n k)) := by
        apply ENNReal.tsum_le_tsum
        intro k
        apply mul_le_mul' le_rfl
        exact (Real.volume_le_diam _).trans ((ediam_closure _).le.trans (hf.ediam_image_le _))
      _ = (L : ℝ≥0∞) * ∑' k, ediam (T n k) ^ (2 : ℕ) := by
        simp_rw [mul_left_comm (ediam _) (L : ℝ≥0∞), ← pow_two]
        exact ENNReal.tsum_mul_left
      _ ≤ (L : ℝ≥0∞) * ((μH[2] : Measure X) A + δ) := by
        exact mul_le_mul' le_rfl (hcost n).le
  refine ⟨fun y => liminf (fun n => g n y) atTop, Measurable.liminf hgm,
    hausdorff_one_fiber_le_liminf_cover A f ε hεlim T hdiam hcover, ?_⟩
  apply (lintegral_liminf_le hgm).trans
  have hm : liminf (fun n => ∫⁻ y, g n y) atTop ≤
      liminf (fun _ : ℕ => (L : ℝ≥0∞) * ((μH[2] : Measure X) A + δ)) atTop :=
    liminf_le_liminf (Eventually.of_forall hgint)
  simpa only [liminf_const] using hm

lemma exists_exact_lipschitz_length_fiber_majorant
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) (hA : (μH[2] : Measure X) A < ∞)
    (L : ℝ≥0) (f : X → ℝ) (hf : LipschitzWith L f) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
      (∀ y, (μH[1] : Measure X) (A ∩ f ⁻¹' {y}) ≤ G y) ∧
      (∫⁻ y, G y) ≤ (L : ℝ≥0∞) * (μH[2] : Measure X) A := by
  let δ : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / (n + 1 : ℝ))
  have hδ : ∀ n, 0 < δ n := fun n => ENNReal.ofReal_pos.mpr (by positivity)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose G hG hbound hint using fun n => exists_lipschitz_length_fiber_majorant A hA L f hf (δ n) (hδ n)
  refine ⟨fun y => ⨅ n, G n y, Measurable.iInf hG,
    (fun y => le_iInf (fun n => hbound n y)), ?_⟩
  have ht : Tendsto (fun n => (L : ℝ≥0∞) * ((μH[2] : Measure X) A + δ n)) atTop
      (𝓝 ((L : ℝ≥0∞) * (μH[2] : Measure X) A)) := by
    simpa only [add_zero] using
      ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hδlim) (Or.inr ENNReal.coe_ne_top)
  apply ge_of_tendsto' ht
  intro n
  exact (lintegral_mono (fun y => iInf_le (fun k => G k y) n)).trans (hint n)

end CircleDomainRigidity

end

end OAI
