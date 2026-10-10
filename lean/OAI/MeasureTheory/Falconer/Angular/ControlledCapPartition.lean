import OAI.MeasureTheory.Falconer.Fourier.AmbientSymbols
import OAI.MeasureTheory.Falconer.Angular.CapNet

namespace OAI

/-!
# A smooth cap partition with controlled number and overlap

The ambient-dimensional count is sufficient for summing arbitrary-power
errors. The positive retained-graph estimate uses the partition identity
and therefore incurs no cap-count factor.

The partition is smooth in every adapted chart.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem controlled_smooth_cap_partition (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (S : Finset (Sphere (n+2))) (η : Sphere (n+2) → Sphere (n+2) → ℝ),
      (S.card : ℝ) ≤ (4/δ+1)^(n+2) ∧
      (∀ w, ((S.filter (fun c => dist w c ≤ δ)).card : ℝ) ≤ (5 : ℝ)^(n+2)) ∧
      (∀ c, Measurable (η c)) ∧
      (∀ w, ∑ c ∈ S, η c w = 1) ∧
      (∀ c ∈ S, ∀ w, 0 ≤ η c w ∧ η c w ≤ 1) ∧
      (∀ c ∈ S, ∀ w, η c w ≠ 0 → ‖(w : Space (n+2))-(c : Space (n+2))‖ ≤ δ) ∧
      (∀ c, ∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n,
        ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => (η c w : ℂ)) y)) := by
  obtain ⟨S,_hsep,hcover,hcard,hoverlap⟩ := finite_separated_cap_net (n+2) hδ
  obtain ⟨F,hF,hpartition,hbounds,hsupport⟩ := smooth_cap_partition_on_net (n+2) hδ S hcover
  refine ⟨S,fun c w => F c w,hcard,hoverlap,?_,hpartition,hbounds,
    (fun c hc w => hsupport c hc w),?_⟩
  · intro c
    exact (hF c).continuous.measurable.comp continuous_subtype_val.measurable
  · intro c e y
    exact ambient_symbol_chart_smooth e (fun x => (F c x : ℂ))
      (Complex.ofRealCLM.contDiff.comp (hF c)) y

end Falconer

end OAI
