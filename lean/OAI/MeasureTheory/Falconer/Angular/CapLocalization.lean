import OAI.MeasureTheory.Falconer.Angular.CapSupport
import OAI.MeasureTheory.Falconer.Estimates.AdaptedFailure

namespace OAI

/-!
# Nonstationarity on a geometric cap after point replacement

The frame depends only on the cap center and center displacement.
Support and the phase lower bound are proved from the geometric cap and
the original point-replacement error. Only amplitude regularity remains
as local analytic data.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem failed_cap_sphere_nonstationary (hpublished : PublishedGnomonicSurface)
    (n m : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (w d : Space (n+2)) (τ δ : ℝ),
      ‖w‖ = 1 → 0 < τ → 0 ≤ δ → δ ≤ 1/2 → τ < ‖perpendicularPart w d‖ →
      ∃ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), e (chartPole n) = w ∧
        ∀ (v : Space (n+2)) (b : Sphere (n+2) → ℂ), Measurable b →
          (∀ z, b z ≠ 0 → ‖(z : Space (n+2))-w‖ ≤ δ) →
          (∀ y : Space n, ‖y‖ ≤ 1 → ContDiff ℝ ∞ (rotatedChartAmplitude e b y)) →
          ∀ (M C D Λ : ℝ), 0 ≤ C → 1 ≤ D → 0 < Λ →
          (∀ z, ‖b z‖ ≤ M) → ‖v‖ ≤ (τ/4)*D →
          ‖v-d‖+8*δ*‖d‖ ≤ τ/2 →
          (∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (rotatedChartAmplitude e b y),
            ‖iteratedDeriv k (rotatedChartAmplitude e b y) u‖ ≤ C*D^k) →
          ‖∫ z : Sphere (n+2),
            Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (z : Space (n+2)) v : ℂ))*b z
            ∂sphereMeasure (n+2)‖ ≤ A*C*(D/(Λ*(τ/4)))^m := by
  obtain ⟨A,hA,he⟩ := failed_test_sphere_nonstationary hpublished n m hn
  refine ⟨A,hA,?_⟩
  intro w d τ δ hw hτ hδ hδsmall hbad
  obtain ⟨e,hew,hestimate⟩ := he w d τ hw hτ hbad
  refine ⟨e,hew,?_⟩
  intro v b hb hcap hsmooth M C D Λ hC hD hΛ hM hv herr hder
  have hc : ∀ z, b z ≠ 0 → ‖(z : Space (n+2))-e (chartPole n)‖ ≤ δ := by
    simpa only [hew] using hcap
  obtain ⟨hs,hout,hsupport⟩ := cap_amplitude_chart_support e b hδ hδsmall hc
  apply hestimate v b hb hs hout hsmooth (fun y _ => hsupport y)
    M C D Λ hC hD hΛ hM hv
  · intro y _ u hu
    have hr := cap_amplitude_chart_radius e b hδ hδsmall hc y u hu
    refine ⟨hr.trans (by linarith),?_⟩
    have hm := mul_le_mul_of_nonneg_right hr (norm_nonneg d)
    nlinarith
  · exact hder

end Falconer

end OAI
