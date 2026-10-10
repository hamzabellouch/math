import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace OAI

open MeasureTheory Filter Set

namespace Invariant233.Fields

theorem projection_diagonal_mem_Icc
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {p : E →L[ℂ] E} (hp : IsStarProjection p) {e : E} (he : ‖e‖ = 1) :
    0 ≤ (inner ℂ (p e) e).re ∧ (inner ℂ (p e) e).re ≤ 1 := by
  refine ⟨(ContinuousLinearMap.IsPositive.of_isStarProjection hp).re_inner_nonneg_left e, ?_⟩
  have h := (ContinuousLinearMap.IsPositive.of_isStarProjection hp.one_sub).re_inner_nonneg_left e
  simp only [sub_apply, one_apply_eq_self,
    inner_sub_left, map_sub, inner_self_eq_norm_sq_to_K, he] at h
  norm_num at h ⊢
  linarith

theorem ae_strict_diagonal_of_ergodic
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsProbabilityMeasure μ]
    {σ : Y → Y} (hσ : Ergodic σ μ) {r : Y → ℝ}
    (hr : Measurable r)
    (hrange : ∀ᵐ y ∂μ, 0 ≤ r y ∧ r y ≤ 1)
    (hmean0 : 0 < ∫ y, r y ∂μ) (hmean1 : (∫ y, r y ∂μ) < 1)
    (hzero : ∀ᵐ y ∂μ, r (σ y) = 0 → r y = 0)
    (hone : ∀ᵐ y ∂μ, r y = 1 → r (σ y) = 1) :
    ∀ᵐ y ∂μ, 0 < r y ∧ r y < 1 := by
  have hmeas0 : MeasurableSet {y | r y = 0} := hr (measurableSet_singleton 0)
  have hmeas1 : MeasurableSet {y | r y = 1} := hr (measurableSet_singleton 1)
  have hz : ∀ᵐ y ∂μ, r y ≠ 0 := by
    rcases hσ.ae_empty_or_univ_of_preimage_ae_le hmeas0.nullMeasurableSet hzero with h | h
    · filter_upwards [h] with y hy
      change (r y = 0) = False at hy
      exact fun hz => hy ▸ hz
    · have heq : r =ᵐ[μ] fun _ => 0 := by
        filter_upwards [h] with y hy
        change (r y = 0) = True at hy
        exact hy.symm ▸ True.intro
      have hi : (∫ y, r y ∂μ) = 0 := by
        rw [integral_congr_ae heq]
        simp
      linarith
  have ho : ∀ᵐ y ∂μ, r y ≠ 1 := by
    rcases hσ.ae_empty_or_univ_of_ae_le_preimage hmeas1.nullMeasurableSet hone with h | h
    · filter_upwards [h] with y hy
      change (r y = 1) = False at hy
      exact fun hz => hy ▸ hz
    · have heq : r =ᵐ[μ] fun _ => 1 := by
        filter_upwards [h] with y hy
        change (r y = 1) = True at hy
        exact hy.symm ▸ True.intro
      have hi : (∫ y, r y ∂μ) = 1 := by
        rw [integral_congr_ae heq]
        simp
      linarith
  filter_upwards [hrange, hz, ho] with y hy hy0 hy1
  exact ⟨lt_of_le_of_ne hy.1 (Ne.symm hy0), lt_of_le_of_ne hy.2 hy1⟩

theorem tendsto_measure_small_of_ae_pos
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsFiniteMeasure μ]
    {r : Y → ℝ} (hr : Measurable r) (hpos : ∀ᵐ y ∂μ, 0 < r y) :
    Tendsto (fun n : ℕ => μ {y | r y < 1 / ((n : ℝ) + 1)}) atTop (nhds 0) := by
  let s : ℕ → Set Y := fun n => {y | r y < 1 / ((n : ℝ) + 1)}
  have hsm : ∀ n, NullMeasurableSet (s n) μ := fun n =>
    (hr measurableSet_Iio).nullMeasurableSet
  have hanti : Antitone s := by
    intro n m hnm y hy
    change r y < 1 / ((m : ℝ) + 1) at hy
    change r y < 1 / ((n : ℝ) + 1)
    apply hy.trans_le
    gcongr
  have hnull : μ (⋂ n, s n) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hpos] with y hy
    intro hmem
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hy
    exact lt_asymm (mem_iInter.mp hmem n) hn
  have ht := tendsto_measure_iInter_atTop hsm hanti ⟨0, measure_ne_top μ (s 0)⟩
  simpa only [Function.comp_def, hnull] using ht

theorem tendsto_measure_diagonal_endpoints
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsFiniteMeasure μ]
    {r : Y → ℝ} (hr : Measurable r)
    (hint : ∀ᵐ y ∂μ, 0 < r y ∧ r y < 1) :
    Tendsto (fun n : ℕ => μ {y | r y < 1 / ((n : ℝ) + 1)}) atTop (nhds 0) ∧
    Tendsto (fun n : ℕ => μ {y | 1 - r y < 1 / ((n : ℝ) + 1)}) atTop (nhds 0) := by
  refine ⟨tendsto_measure_small_of_ae_pos hr (hint.mono fun _ h => h.1), ?_⟩
  apply tendsto_measure_small_of_ae_pos (measurable_const.sub hr)
  filter_upwards [hint] with y hy
  exact sub_pos.mpr hy.2

end Invariant233.Fields

end OAI
