import OAI.MeasureTheory.Falconer.Estimates.RotatedNonstationary

namespace OAI

/-!
# A single adapted chart for a discarded cell--cap term

The frame is chosen using the cap center and the center displacement.
It works simultaneously for every point displacement allowed by the
cell-replacement error. No choice depends on an individual point pair.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem failed_test_adapted_phase_lower {n : ℕ} {w d : Space (n+2)}
    (hw : ‖w‖ = 1) {τ : ℝ} (hτ : 0 < τ)
    (hbad : τ < ‖perpendicularPart w d‖) :
    ∃ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), e (chartPole n) = w ∧
      ∀ (y : Space n) (v : Space (n+2)) (u : ℝ),
        ‖transverseLift y+u•chartAxis n‖ ≤ 1 →
        ‖v-d‖+4*‖transverseLift y+u•chartAxis n‖*‖d‖ ≤ τ/2 →
        τ/4 ≤ |deriv (fun x => inner ℝ
          (normalizedLine (chartPole n+transverseLift y) (chartAxis n) x) (e.symm v)) u| := by
  obtain ⟨t,ht,hwt,hl⟩ := perpendicular_failure_chart_nonstationary hw hτ hbad
  obtain ⟨e,he₀,he₁⟩ := exists_adapted_chart_frame hw ht hwt
  refine ⟨e,he₀,?_⟩
  intro y v u hsmall herr
  have hy : inner ℝ w (e (transverseLift y)) = 0 := by
    rw [← he₀,e.inner_map_map]
    exact chartPole_inner_transverse y
  have heq : ‖e (transverseLift y)+u•t‖ = ‖transverseLift y+u•chartAxis n‖ := by
    rw [← he₁,← e.map_smul,← e.map_add,e.norm_map]
  have hsmall' : ‖e (transverseLift y)+u•t‖ ≤ 1 := by rw [heq]; exact hsmall
  have herr' : ‖v-d‖+4*‖e (transverseLift y)+u•t‖*‖d‖ ≤ τ/2 := by
    rw [heq]
    exact herr
  have hh := hl (e (transverseLift y)) v u hy hsmall' herr'
  have hp : (fun x => inner ℝ (normalizedLine (w+e (transverseLift y)) t x) v) =
      (fun x => inner ℝ
        (normalizedLine (chartPole n+transverseLift y) (chartAxis n) x) (e.symm v)) := by
    funext x
    rw [← he₀,← he₁,← e.map_add,normalizedLine_isometry,inner_isometry_pullback]
  rw [hp] at hh
  exact hh

theorem failed_test_sphere_nonstationary (hpublished : PublishedGnomonicSurface)
    (n m : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (w d : Space (n+2)) (τ : ℝ),
      ‖w‖ = 1 → 0 < τ → τ < ‖perpendicularPart w d‖ →
      ∃ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), e (chartPole n) = w ∧
        ∀ (v : Space (n+2)) (b : Sphere (n+2) → ℂ), Measurable b →
          (∀ z, sphereMap e.symm z ∉ northHemisphere (n+1) → b z = 0) →
          (∀ y : Space n, 1 < ‖y‖ → ∀ u, rotatedChartAmplitude e b y u = 0) →
          (∀ y : Space n, ‖y‖ ≤ 1 → ContDiff ℝ ∞ (rotatedChartAmplitude e b y)) →
          (∀ y : Space n, ‖y‖ ≤ 1 →
            tsupport (rotatedChartAmplitude e b y) ⊆ Icc (-1 : ℝ) 1) →
          ∀ (M C D Λ : ℝ), 0 ≤ C → 1 ≤ D → 0 < Λ →
          (∀ z, ‖b z‖ ≤ M) → ‖v‖ ≤ (τ/4)*D →
          (∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (rotatedChartAmplitude e b y),
            ‖transverseLift y+u•chartAxis n‖ ≤ 1 ∧
            ‖v-d‖+4*‖transverseLift y+u•chartAxis n‖*‖d‖ ≤ τ/2) →
          (∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (rotatedChartAmplitude e b y),
            ‖iteratedDeriv k (rotatedChartAmplitude e b y) u‖ ≤ C*D^k) →
          ‖∫ z : Sphere (n+2),
            Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (z : Space (n+2)) v : ℂ))*b z
            ∂sphereMeasure (n+2)‖ ≤ A*C*(D/(Λ*(τ/4)))^m := by
  obtain ⟨A,hA,he⟩ := rotated_sphere_chart_nonstationary hpublished n m hn
  refine ⟨A,hA,?_⟩
  intro w d τ hw hτ hbad
  obtain ⟨e,hew,hl⟩ := failed_test_adapted_phase_lower hw hτ hbad
  refine ⟨e,hew,?_⟩
  intro v b hb hs hout hsmooth hsupport M C D Λ hC hD hΛ hM hv herr hder
  apply he e v b hb hs hout hsmooth hsupport M C D Λ (τ/4) hC hD hΛ
    (by positivity) hM hv
  · intro y hy u hu
    exact hl y v u (herr y hy u hu).1 (herr y hy u hu).2
  · exact hder

end Falconer

end OAI
