import OAI.MeasureTheory.Falconer.Fourier.QuadraticIntegral
import OAI.MeasureTheory.Falconer.Fourier.PublishedQuadraticStationary
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

/-!
# Applying the quadratic expansion to the actual sphere integral

The amplitude is the explicitly computed surface density times the spherical
amplitude, extended by zero from the fixed unit chart. Smoothness and its
quantitative derivative bounds are retained as local obligations. The only
published inputs are the gnomonic measure formula and the fixed Euclidean
quadratic stationary-phase theorem.
-/

namespace Falconer
open Set MeasureTheory Metric
open scoped BigOperators ContDiff

noncomputable def quadraticAmplitude (m : ℕ) (b : Sphere (m+3) → ℂ) :
    Space (m+2) → ℂ :=
  (Metric.ball (0 : Space (m+2)) 1).indicator (fun u =>
    ((Real.sqrt (1-‖u‖^2/4))^m : ℂ) * b (gnomonicChart (quadraticToGnomonic u)))

theorem quadraticAmplitude_tsupport (m : ℕ) (b : Sphere (m+3) → ℂ) :
    tsupport (quadraticAmplitude m b) ⊆ Metric.closedBall (0 : Space (m+2)) 1 := by
  apply closure_minimal _ isClosed_closedBall
  exact Set.support_indicator_subset.trans Metric.ball_subset_closedBall

theorem quadraticAmplitude_hasCompactSupport (m : ℕ) (b : Sphere (m+3) → ℂ) :
    HasCompactSupport (quadraticAmplitude m b) := by
  exact (isCompact_closedBall (0 : Space (m+2)) 1).of_isClosed_subset
    isClosed_closure (quadraticAmplitude_tsupport m b)

/-- A mask that vanishes in the outer half of the fixed chart removes the
boundary issue in extending its chart amplitude by zero. -/
theorem quadraticAmplitude_contDiff (m : ℕ) (b : Sphere (m+3) → ℂ)
    (hb : ContDiffOn ℝ ∞
      (fun u : Space (m+2) => b (gnomonicChart (quadraticToGnomonic u)))
      (Metric.ball (0 : Space (m+2)) 1))
    (hmask : ∀ u : Space (m+2), (1:ℝ)/2 ≤ ‖u‖ → ‖u‖ < 1 →
      b (gnomonicChart (quadraticToGnomonic u)) = 0) :
    ContDiff ℝ ∞ (quadraticAmplitude m b) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : ‖u‖ < 1
  · have hum : u ∈ Metric.ball (0 : Space (m+2)) 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hu
    have hsq : ‖u‖^2 < 1 := by
      simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
    have hd : ContDiffAt ℝ ∞
        (fun v : Space (m+2) => ((Real.sqrt (1-‖v‖^2/4))^m : ℂ)) u := by
      apply ContDiffAt.pow
      exact Complex.ofRealCLM.contDiff.comp_contDiffAt u
        ((contDiffAt_const.sub ((contDiff_norm_sq ℝ).contDiffAt.div_const 4)).sqrt
          (by linarith : 1-‖u‖^2/4 ≠ 0))
    apply (hd.mul ((hb u hum).contDiffAt (isOpen_ball.mem_nhds hum))).congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hum] with v hv
    simp only [quadraticAmplitude, indicator_of_mem hv]
  · have hlarge : (1:ℝ)/2 < ‖u‖ := by linarith
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hlarge] with v hv
    by_cases hvin : v ∈ Metric.ball (0 : Space (m+2)) 1
    · have hvnorm : ‖v‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using hvin
      simp only [quadraticAmplitude, indicator_of_mem hvin,
        hmask v (le_of_lt hv) hvnorm, mul_zero]
    · simp only [quadraticAmplitude, indicator_of_notMem hvin]

theorem quadraticAmplitude_derivatives_bounded (m M : ℕ) (b : Sphere (m+3) → ℂ)
    (hb : ContDiff ℝ ∞ (quadraticAmplitude m b)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ≤ M, ∀ x,
      ‖iteratedFDeriv ℝ k (quadraticAmplitude m b) x‖ ≤ B := by
  exact (quadraticAmplitude_hasCompactSupport m b).exists_bound_iteratedFDeriv hb M

noncomputable def quadraticSphereOscillation (m : ℕ) (Λ : ℝ)
    (b : Sphere (m+3) → ℂ) : ℂ :=
  ∫ w : Sphere (m+3),
    Complex.exp (Complex.I*(Λ : ℂ)*
      (inner ℝ (w : Space (m+3)) (coordinateJoin (0 : Space (m+2)) 1) : ℂ)) * b w
    ∂sphereMeasure (m+3)

theorem quadraticSphereOscillation_eq (hgnomonic : PublishedGnomonicSurface)
    (m : ℕ) (Λ : ℝ) (b : Sphere (m+3) → ℂ) (hb : Measurable b)
    (hs : ∀ w, w ∉ northHemisphere (m+2) → b w = 0)
    (hchart : ∀ x : Space (m+2),
      x ∉ quadraticToGnomonic '' Metric.ball (0 : Space (m+2)) 1 →
        b (gnomonicChart x) = 0) :
    quadraticSphereOscillation m Λ b = Complex.exp (Complex.I*(Λ : ℂ)) *
      ∫ u : Space (m+2), Complex.exp (-(Complex.I*(Λ : ℂ)/2)*(‖u‖^2 : ℝ)) *
        quadraticAmplitude m b u := by
  rw [quadraticSphereOscillation,
    quadratic_sphere_oscillatory_integral hgnomonic m Λ b hb hs hchart]
  congr 1
  have heq : (fun u : Space (m+2) =>
      Complex.exp (-(Complex.I*(Λ : ℂ)/2)*(‖u‖^2 : ℝ)) * quadraticAmplitude m b u) =
      (Metric.ball (0 : Space (m+2)) 1).indicator (fun u =>
        Complex.exp (-(Complex.I*(Λ : ℂ)/2)*(‖u‖^2 : ℝ)) *
          ((Real.sqrt (1-‖u‖^2/4))^m : ℂ) *
            b (gnomonicChart (quadraticToGnomonic u))) := by
    funext u
    by_cases hu : u ∈ Metric.ball (0 : Space (m+2)) 1
    · simp [quadraticAmplitude, hu, mul_assoc]
    · simp [quadraticAmplitude, hu]
  rw [heq, integral_indicator measurableSet_ball]

/-- The published Euclidean estimate bounds the spherical
oscillation. No spherical coefficient formula is presupposed: the jets on
the right are the actual iterated Euclidean Laplacians of the chart amplitude. -/
theorem quadraticSphereOscillation_remainder
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) (hJ : 1 ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Sphere (m+3) → ℂ), Measurable b →
      (∀ w, w ∉ northHemisphere (m+2) → b w = 0) →
      (∀ x : Space (m+2),
        x ∉ quadraticToGnomonic '' Metric.ball (0 : Space (m+2)) 1 →
          b (gnomonicChart x) = 0) →
      ContDiff ℝ ∞ (quadraticAmplitude m b) →
      ∀ B : ℝ, 0 ≤ B →
        (∀ k ≤ 2*J+(m+2)+1, ∀ x,
          ‖iteratedFDeriv ℝ k (quadraticAmplitude m b) x‖ ≤ B) →
        ∀ Λ : ℝ, 1 ≤ Λ →
          ‖((Λ ^ (((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ) *
              Complex.exp (-(Complex.I*(Λ : ℂ))) * quadraticSphereOscillation m Λ b -
            ∑ j ∈ Finset.range J,
              ((Λ ^ (-(j : ℝ)) : ℝ) : ℂ) *
                quadraticJetCoefficient j (quadraticAmplitude m b)‖ ≤
            C * Λ ^ (-(J : ℝ)) * B := by
  obtain ⟨C, hC, hrem⟩ := hquadratic (m+2) J (by omega) hJ
  refine ⟨C, hC, ?_⟩
  intro b hb hs hchart ha B hB hder Λ hΛ
  have he := quadraticSphereOscillation_eq hgnomonic m Λ b hb hs hchart
  rw [he]
  have hcancel : Complex.exp (-(Complex.I*(Λ : ℂ))) *
      Complex.exp (Complex.I*(Λ : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  have halg (s z : ℂ) : s * Complex.exp (-(Complex.I*(Λ : ℂ))) *
      (Complex.exp (Complex.I*(Λ : ℂ)) * z) = s*z := by
    rw [mul_assoc, ← mul_assoc (Complex.exp _), hcancel, one_mul]
  rw [halg]
  exact hrem (quadraticAmplitude m b) ha (quadraticAmplitude_tsupport m b) B hB hder Λ hΛ

end Falconer

end OAI
