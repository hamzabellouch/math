import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma integrable_of_nonneg_ae_limit {u : ℕ → α → ℝ} {f : α → ℝ}
    (hi : ∀ n, Integrable (u n) μ) (hf : AEStronglyMeasurable f μ)
    (h0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ u n x) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (f x)))
    {C : ℝ} (hb : ∀ n, (∫ x, u n x ∂μ) ≤ C) : Integrable f μ := by
  refine ⟨hf, (hasFiniteIntegral_iff_ofReal hf0).mpr ?_⟩
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  calc
    _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (u n x)) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ht] with x hx
      exact ((ENNReal.continuous_ofReal.tendsto (f x)).comp hx).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (u n x) ∂μ) atTop :=
      lintegral_liminf_le' (fun n => ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        (hi n).aestronglyMeasurable.aemeasurable)
    _ ≤ ENNReal.ofReal C := by
      apply liminf_le_of_frequently_le'
      exact (Eventually.of_forall fun n => by
        rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (h0 n)]
        exact ENNReal.ofReal_le_ofReal (hb n)).frequently

end CoulombAtom

end

end OAI
