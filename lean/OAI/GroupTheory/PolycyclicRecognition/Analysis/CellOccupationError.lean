import OAI.GroupTheory.PolycyclicRecognition.Algebra.OccupationWeakLimit
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! # Finite-cell errors for occupation observables

The observable may vary with the scale. Only its common bound matters,
so the estimate survives projection from nonunique factor coordinates.
-/

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology symmDiff

/-- Changing a finite sampling cell changes a bounded observable integral
by at most its bound times the measure of the symmetric difference. -/
theorem norm_setIntegral_sub_le_symmDiff
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : μ s < ⊤) (hft : μ t < ⊤)
    (f : X → E) (hf : AEStronglyMeasurable f μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) :
    ‖(∫ x in s, f x ∂μ) - ∫ x in t, f x ∂μ‖ ≤ C * (μ (s ∆ t)).toReal := by
  have his : IntegrableOn f s μ :=
    IntegrableOn.of_bound hfs hf.restrict C (Eventually.of_forall hb)
  have hit : IntegrableOn f t μ :=
    IntegrableOn.of_bound hft hf.restrict C (Eventually.of_forall hb)
  have hd : μ (s ∆ t) < ⊤ := lt_of_le_of_lt (measure_mono symmDiff_subset_union)
    ((measure_union_le s t).trans_lt (ENNReal.add_lt_top.mpr ⟨hfs, hft⟩))
  have hic : IntegrableOn (fun _ : X => C) (s ∆ t) μ :=
    IntegrableOn.of_bound hd aestronglyMeasurable_const C
      (Eventually.of_forall (fun _ => by simp [Real.norm_eq_abs, abs_of_nonneg hC]))
  rw [← integral_indicator hs, ← integral_indicator ht,
    ← integral_sub (his.integrable_indicator hs) (hit.integrable_indicator ht)]
  have hbound : ∀ x, ‖s.indicator f x - t.indicator f x‖ ≤
      (s ∆ t).indicator (fun _ => C) x := by
    intro x
    by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxs, hxt,
        Set.mem_symmDiff, hb x]
  calc
    _ ≤ ∫ x, (s ∆ t).indicator (fun _ => C) x ∂μ :=
      norm_integral_le_of_norm_le (hic.integrable_indicator (hs.symmDiff ht))
        (Eventually.of_forall hbound)
    _ = C * (μ (s ∆ t)).toReal := by
      rw [integral_indicator (hs.symmDiff ht), setIntegral_const]
      simp only [smul_eq_mul, measureReal_def, mul_comm]

/-- A measure-preserving change of sampling coordinates has an error
controlled solely by the symmetric difference of the finite cell. -/
theorem norm_cell_translation_integral_error_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : X → X) (hT : MeasurePreserving T μ μ)
    {s : Set X} (hs : MeasurableSet s) (hfin : μ s < ⊤)
    (f : X → ℝ) (hf : AEStronglyMeasurable f μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) :
    ‖(∫ x in s, f (T x) ∂μ) - ∫ x in s, f x ∂μ‖ ≤
      C * (μ ((T ⁻¹' s) ∆ s)).toReal := by
  have hpre : μ (T ⁻¹' s) = μ s := hT.measure_preimage hs.nullMeasurableSet
  have heq : (∫ x in T ⁻¹' s, f (T x) ∂μ) = ∫ x in s, f x ∂μ := by
    have hfm : AEStronglyMeasurable f (Measure.map T μ) := by rwa [hT.map_eq]
    have hh := setIntegral_map hs hfm hT.measurable.aemeasurable
    rw [hT.map_eq] at hh
    exact hh.symm
  rw [← heq, norm_sub_rev]
  exact norm_setIntegral_sub_le_symmDiff μ (hT.measurable hs) hs
    (hpre ▸ hfin) hfin (fun x => f (T x))
    (hf.comp_measurePreserving hT) hC (fun x => hb (T x))

/-- Vanishing boundary loss makes every uniformly bounded, scale-dependent
sampling observable asymptotically translation invariant. -/
theorem cell_translation_integral_error_tendsto_zero
    {X ι : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : ι → X → X) (hT : ∀ i, MeasurePreserving (T i) μ μ)
    {s : Set X} (hs : MeasurableSet s) (hfin : μ s < ⊤)
    (f : ι → X → ℝ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i x, ‖f i x‖ ≤ C)
    {l : Filter ι}
    (hcell : Tendsto (fun i => μ (((T i) ⁻¹' s) ∆ s)) l (𝓝 0)) :
    Tendsto (fun i => (∫ x in s, f i (T i x) ∂μ) - ∫ x in s, f i x ∂μ)
      l (𝓝 0) := by
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hcell
  have hlim : Tendsto (fun i => C * (μ (((T i) ⁻¹' s) ∆ s)).toReal) l (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun i =>
      norm_cell_translation_integral_error_le μ (T i) (hT i) hs hfin
        (f i) (hf i) hC (hb i))) hlim

end PolycyclicRecognition

end OAI
