import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense

namespace OAI

/-! # Small measure-preserving moves of an integrable density

The minimum of the moved density and the original one is dominated by the
original density. Thus dominated convergence gives L1 convergence without
requiring a common compact support for all moved densities.
-/

namespace PolycyclicRecognition

open MeasureTheory Filter
open scoped Topology

/-- A nonnegative continuous integrable density changes by a vanishing L1
amount under measure-preserving maps tending pointwise to the identity. -/
theorem density_translation_l1_tendsto_zero
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (ρ : X → ℝ) (hc : Continuous ρ) (hi : Integrable ρ μ)
    (hp : ∀ x, 0 ≤ ρ x)
    {l : Filter ι} [l.IsCountablyGenerated]
    (T : ι → X → X) (hT : ∀ i, MeasurePreserving (T i) μ μ)
    (hlim : ∀ x, Tendsto (fun i => T i x) l (𝓝 x)) :
    Tendsto (fun i => ∫ x, |ρ (T i x) - ρ x| ∂μ) l (𝓝 0) := by
  let f : ι → X → ℝ := fun i x => min (ρ (T i x)) (ρ x)
  have hfmeas (i : ι) : AEStronglyMeasurable (f i) μ :=
    (hc.measurable.comp (hT i).measurable).min hc.measurable |>.aestronglyMeasurable
  have hfbound (i : ι) : ∀ x, ‖f i x‖ ≤ ρ x := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp _) (hp _))]
    exact min_le_right _ _
  have hfi (i : ι) : Integrable (f i) μ :=
    hi.mono' (hfmeas i) (Eventually.of_forall (hfbound i))
  have hfconv : Tendsto (fun i => ∫ x, f i x ∂μ) l (𝓝 (∫ x, ρ x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence ρ
      (Eventually.of_forall hfmeas) (Eventually.of_forall (fun i =>
        Eventually.of_forall (hfbound i))) hi
    exact Eventually.of_forall (fun x => by
      have ht : Tendsto (fun i => min (ρ (T i x)) (ρ x)) l (𝓝 (min (ρ x) (ρ x))) :=
        ((hc.tendsto x).comp (hlim x)).min tendsto_const_nhds
      simpa only [f, min_self] using ht)
  have hmoved (i : ι) : Integrable (fun x => ρ (T i x)) μ :=
    (hT i).integrable_comp_of_integrable hi
  have hmass (i : ι) : (∫ x, ρ (T i x) ∂μ) = ∫ x, ρ x ∂μ := by
    have hρ : AEStronglyMeasurable ρ (Measure.map (T i) μ) := by
      rw [(hT i).map_eq]
      exact hi.aestronglyMeasurable
    have h := integral_map (hT i).measurable.aemeasurable hρ
    rw [(hT i).map_eq] at h
    exact h.symm
  have heq (i : ι) : (∫ x, |ρ (T i x) - ρ x| ∂μ) =
      (∫ x, ρ x ∂μ) + (∫ x, ρ x ∂μ) - 2 * (∫ x, f i x ∂μ) := by
    have hpoint (x : X) : |ρ (T i x) - ρ x| = ρ (T i x) + ρ x - 2 * f i x := by
      dsimp only [f]
      rcases le_total (ρ (T i x)) (ρ x) with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]
        ring
      · rw [abs_of_nonneg (sub_nonneg.mpr h), min_eq_right h]
        ring
    rw [integral_congr_ae (Eventually.of_forall hpoint)]
    have hsub := integral_sub ((hmoved i).add hi) ((hfi i).const_mul 2)
    simp only [Pi.add_apply] at hsub
    rw [hsub]
    have hadd := integral_add (hmoved i) hi
    rw [hadd, integral_const_mul, hmass]
  have ht : Tendsto (fun i => (∫ x, ρ x ∂μ) + (∫ x, ρ x ∂μ) - 2 * (∫ x, f i x ∂μ))
      l (𝓝 ((∫ x, ρ x ∂μ) + (∫ x, ρ x ∂μ) - 2 * (∫ x, ρ x ∂μ))) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hfconv)
  have he : (∫ x, ρ x ∂μ) + (∫ x, ρ x ∂μ) - 2 * (∫ x, ρ x ∂μ) = 0 := by ring
  rw [he] at ht
  exact ht.congr (fun i => (heq i).symm)

end PolycyclicRecognition

end OAI
