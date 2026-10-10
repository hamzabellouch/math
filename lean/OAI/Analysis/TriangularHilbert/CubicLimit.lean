import OAI.Analysis.TriangularHilbert.CubicApprox

namespace OAI

universe uα

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

lemma tendsto_integral_cubes (f : ℝ×ℝ → ℂ) (g : ℕ → ℝ×ℝ → ℂ) (hg : ∀ n, Continuous (g n))
    {D : ℝ×ℝ → ℝ} (hD : Integrable D)
    (hb : ∀ᵐ z : ℝ×ℝ, (∀ n, ‖g n z‖^3 ≤ D z) ∧ Tendsto (fun n => g n z) atTop (𝓝 (f z))) :
    Tendsto (fun n => ∫ z : ℝ×ℝ, ‖g n z‖^3) atTop (𝓝 (∫ z : ℝ×ℝ, ‖f z‖^3)) := by
  apply tendsto_integral_of_dominated_convergence D (fun n => (hg n).norm.pow 3 |>.aestronglyMeasurable) hD
  · intro n
    filter_upwards [hb] with z hz
    simpa only [Pi.pow_apply,Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 3)] using hz.1 n
  · filter_upwards [hb] with z hz
    exact hz.2.norm.pow 3

lemma lintegral_le_of_ae_tendsto {α : Type uα} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞} {b : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (hm : ∀ n, AEMeasurable (F n) μ) (ht : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a)))
    (hb : ∀ n, (∫⁻ a, F n a ∂μ) ≤ b n) (hc : Tendsto b atTop (𝓝 c)) :
    (∫⁻ a, f a ∂μ) ≤ c := by
  calc
    (∫⁻ a, f a ∂μ) = ∫⁻ a, liminf (fun n => F n a) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ht] with a ha
      exact ha.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ a, F n a ∂μ) atTop := lintegral_liminf_le' hm
    _ ≤ liminf b atTop := liminf_le_liminf (Eventually.of_forall hb)
    _ = c := hc.liminf_eq
end
end TriangularHilbert
end

end OAI
