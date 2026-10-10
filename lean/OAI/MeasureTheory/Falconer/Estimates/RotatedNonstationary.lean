import OAI.MeasureTheory.Falconer.Angular.SphereNonstationary
import OAI.MeasureTheory.Falconer.Geometry.ChartFrame

namespace OAI

/-!
# Uniform rotation of the spherical nonstationary estimate

The same constant applies to every cap center and every choice of its
first tangent direction. The displacement is pulled back by the linear
isometry, while the amplitude keeps its original point labels.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def rotatedChartAmplitude {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (b : Sphere (n+2) → ℂ)
    (y : Space n) (u : ℝ) : ℂ := chartAmplitude (fun w => b (sphereMap e w)) y u

theorem rotated_sphere_chart_nonstationary (hpublished : PublishedGnomonicSurface)
    (n m : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
      (v : Space (n+2)) (b : Sphere (n+2) → ℂ),
      Measurable b →
      (∀ w, sphereMap e.symm w ∉ northHemisphere (n+1) → b w = 0) →
      (∀ y : Space n, 1 < ‖y‖ → ∀ u, rotatedChartAmplitude e b y u = 0) →
      (∀ y : Space n, ‖y‖ ≤ 1 → ContDiff ℝ ∞ (rotatedChartAmplitude e b y)) →
      (∀ y : Space n, ‖y‖ ≤ 1 → tsupport (rotatedChartAmplitude e b y) ⊆ Icc (-1 : ℝ) 1) →
      ∀ (M C D Λ τ : ℝ), 0 ≤ C → 1 ≤ D → 0 < Λ → 0 < τ →
      (∀ w, ‖b w‖ ≤ M) → ‖v‖ ≤ τ*D →
      (∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (rotatedChartAmplitude e b y),
        τ ≤ |deriv (fun x => inner ℝ
          (normalizedLine (chartPole n + transverseLift y) (chartAxis n) x) (e.symm v)) u|) →
      (∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (rotatedChartAmplitude e b y),
        ‖iteratedDeriv k (rotatedChartAmplitude e b y) u‖ ≤ C*D^k) →
      ‖∫ w : Sphere (n+2),
        Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space (n+2)) v : ℂ)) * b w
        ∂sphereMeasure (n+2)‖ ≤ A*C*(D/(Λ*τ))^m := by
  obtain ⟨A,hA,he⟩ := sphere_chart_nonstationary hpublished n m hn
  refine ⟨A,hA,?_⟩
  intro e v b hb hs hout hsmooth hsupport M C D Λ τ hC hD hΛ hτ hM hv hl hder
  have hrot := he (e.symm v) (fun w => b (sphereMap e w))
    (hb.comp (continuous_sphereMap e).measurable) (by
      intro w hw
      apply hs
      have hh : sphereMap e.symm (sphereMap e w) = w := (sphereHomeomorph e).left_inv w
      rw [hh]
      exact hw) hout hsmooth hsupport M C D Λ τ hC hD hΛ hτ
    (fun w => hM (sphereMap e w)) (by simpa only [e.symm.norm_map] using hv) hl hder
  have hI := sphere_integral_rotation e (fun w : Sphere (n+2) =>
    Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space (n+2)) v : ℂ))*b w)
  rw [← hI]
  convert hrot using 1
  apply congrArg norm
  apply integral_congr_ae
  filter_upwards with w
  congr 3
  exact congrArg (fun r : ℝ => (r : ℂ)) (inner_isometry_pullback e w v)

end Falconer

end OAI
