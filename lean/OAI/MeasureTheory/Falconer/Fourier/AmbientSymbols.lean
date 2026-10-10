import OAI.MeasureTheory.Falconer.Estimates.RotatedNonstationary
import OAI.MeasureTheory.Falconer.Angular.SmoothCapPartition

namespace OAI

/-!
# Ambient smooth symbols in the adapted spherical chart

The smooth cap partition is constructed in Euclidean space. Its restriction
to every rotated one-coordinate spherical chart is smooth, including at
points where the amplitude vanishes.
-/

namespace Falconer
open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalizedLine_contDiff (a t : E) (hne : ∀ u : ℝ, a+u•t ≠ 0) :
    ContDiff ℝ ∞ (normalizedLine a t) := by
  have hz : ContDiff ℝ ∞ (fun u : ℝ => a+u•t) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  exact ((hz.norm ℝ hne).inv (fun u => norm_ne_zero_iff.mpr (hne u))).smul hz

theorem ambient_symbol_chart_smooth {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (F : Space (n+2) → ℂ)
    (hF : ContDiff ℝ ∞ F) (y : Space n) :
    ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => F w) y) := by
  have hn (u : ℝ) : (chartPole n+transverseLift y)+u•chartAxis n ≠ 0 := by
    rw [add_assoc]
    apply tangent_chart_nonzero (chartPole_norm n)
    simp only [inner_add_right,real_inner_smul_right,chartPole_inner_transverse,
      chartPole_inner_axis,mul_zero,add_zero]
  have hp := normalizedLine_contDiff (chartPole n+transverseLift y) (chartAxis n) hn
  have he : ContDiff ℝ ∞ (fun x : Space (n+2) => e x) := e.toContinuousLinearMap.contDiff
  have hc := hF.comp (he.comp hp)
  change ContDiff ℝ ∞ (fun u => F (e (gnomonicChart (coordinateJoin y u))))
  simpa only [Function.comp_def,gnomonicChart_coordinateJoin] using hc

theorem finite_smooth_chart_cap_partition (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (S : Finset (Sphere (n+2))) (η : Sphere (n+2) → Sphere (n+2) → ℝ),
      (∀ c, Measurable (η c)) ∧
      (∀ w, ∑ c ∈ S, η c w = 1) ∧
      (∀ c ∈ S, ∀ w, 0 ≤ η c w ∧ η c w ≤ 1) ∧
      (∀ c ∈ S, ∀ w, η c w ≠ 0 → ‖(w : Space (n+2))-(c : Space (n+2))‖ ≤ δ) ∧
      (∀ c, ∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n,
        ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => (η c w : ℂ)) y)) := by
  obtain ⟨S,F,hF,hpartition,hbounds,hsupport⟩ := finite_smooth_cap_partition (n+2) hδ
  refine ⟨S,fun c w => F c w,?_,hpartition,hbounds,(fun c hc w => hsupport c hc w),?_⟩
  · intro c
    exact (hF c).continuous.measurable.comp continuous_subtype_val.measurable
  · intro c e y
    exact ambient_symbol_chart_smooth e (fun x => (F c x : ℂ))
      (Complex.ofRealCLM.contDiff.comp (hF c)) y

end Falconer

end OAI
