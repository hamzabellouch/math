import OAI.MeasureTheory.Falconer.Angular.SphereChartIntegral
import OAI.MeasureTheory.Falconer.Geometry.ChartCoordinates
import OAI.MeasureTheory.Falconer.Measures.ChartDensityEstimate

namespace OAI

/-!
# A nonstationary estimate for the actual sphere measure

The amplitude is supported in one gnomonic cap. Ordinary one-coordinate
regularity and a phase lower bound give arbitrary repeated-integration
decay, with a constant independent of the cap amplitude and frequency.
The density and the remaining-coordinate integration are included.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def chartAmplitude {n : ℕ} (b : Sphere (n+2) → ℂ)
    (y : Space n) (u : ℝ) : ℂ := b (gnomonicChart (coordinateJoin y u))

theorem sphere_chart_nonstationary (hpublished : PublishedGnomonicSurface)
    (n m : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (v : Space (n+2)) (b : Sphere (n+2) → ℂ),
      Measurable b →
      (∀ w, w ∉ northHemisphere (n+1) → b w = 0) →
      (∀ y : Space n, 1 < ‖y‖ → ∀ u, chartAmplitude b y u = 0) →
      (∀ y : Space n, ‖y‖ ≤ 1 → ContDiff ℝ ∞ (chartAmplitude b y)) →
      (∀ y : Space n, ‖y‖ ≤ 1 → tsupport (chartAmplitude b y) ⊆ Icc (-1 : ℝ) 1) →
      ∀ (M C D Λ τ : ℝ), 0 ≤ C → 1 ≤ D → 0 < Λ → 0 < τ →
      (∀ w, ‖b w‖ ≤ M) → ‖v‖ ≤ τ*D →
      (∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (chartAmplitude b y),
        τ ≤ |deriv (fun x => inner ℝ
          (normalizedLine (chartPole n + transverseLift y) (chartAxis n) x) v) u|) →
      (∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (chartAmplitude b y),
        ‖iteratedDeriv k (chartAmplitude b y) u‖ ≤ C*D^k) →
      ‖∫ w : Sphere (n+2),
        Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space (n+2)) v : ℂ)) * b w
        ∂sphereMeasure (n+2)‖ ≤ A*C*(D/(Λ*τ))^m := by
  obtain ⟨A,hA,hestimate⟩ := density_tangent_chart_nonstationary (E := Space (n+2)) (n+2) m
  let K := Metric.closedBall (0 : Space n) 1
  let V : ℝ := (volume : Measure (Space n)).real K
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  refine ⟨A*V,mul_nonneg hA hV,?_⟩
  intro v b hb hs hout hsmooth hsupport M C D Λ τ hC hD hΛ hτ hM hv hl hder
  let F : Sphere (n+2) → ℂ := fun w =>
    Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space (n+2)) v : ℂ)) * b w
  have hFm : Measurable F := by
    apply Measurable.mul _ hb
    fun_prop
  have hFb (w : Sphere (n+2)) : ‖F w‖ ≤ M := by
    simpa only [F,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.mul_im,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,
      sub_zero,zero_sub,neg_zero,Real.exp_zero,one_mul] using hM w
  have hFi : Integrable F (sphereMeasure (n+2)) :=
    Integrable.of_bound hFm.aestronglyMeasurable M (Filter.Eventually.of_forall hFb)
  let G : Space n → ℂ := fun y => ∫ u : ℝ,
    phaseOscillator (fun x => inner ℝ
      (normalizedLine (chartPole n + transverseLift y) (chartAxis n) x) v) Λ u *
      ((chartDensityKernel (n+2) (‖y‖,u) : ℂ) * chartAmplitude b y u)
  have he : (∫ w, F w ∂sphereMeasure (n+2)) = ∫ y, G y := by
    rw [gnomonic_sphere_iterated_integral hpublished hn F hFm hFi (by
      intro w hw
      simp only [F,hs w hw,mul_zero])]
    apply integral_congr_ae
    filter_upwards with y
    apply integral_congr_ae
    filter_upwards with u
    simp only [F,chartAmplitude,gnomonicChart_coordinateJoin,
      gnomonicDensity_coordinateJoin,phaseOscillator,Complex.real_smul]
    ring
  have hGout (y : Space n) (hy : y ∉ K) : G y = 0 := by
    have hn : 1 < ‖y‖ := by
      simpa only [K,Metric.mem_closedBall,dist_zero_right,not_le] using hy
    simp only [G,hout y hn,mul_zero,integral_zero]
  have hGin (y : Space n) (hy : y ∈ K) : ‖G y‖ ≤ A*C*(D/(Λ*τ))^m := by
    have hy' : ‖y‖ ≤ 1 := by simpa only [K,Metric.mem_closedBall,dist_zero_right] using hy
    have hh := hestimate (chartPole n) (transverseLift y) (chartAxis n) v (chartAmplitude b y)
      (chartPole_norm n) (chartAxis_norm n) (chartPole_inner_transverse y)
      (chartPole_inner_axis n) (transverseLift_inner_axis y)
      (by simpa only [transverseLift_norm] using hy') (hsmooth y hy')
      C D Λ τ hC hD hΛ hτ hv (hsupport y hy') (hl y hy')
      (fun k hk u hu => hder k hk y hy' u hu)
    simpa only [G,transverseLift_norm] using hh
  change ‖∫ w, F w ∂sphereMeasure (n+2)‖ ≤ _
  rw [he,← setIntegral_eq_integral_of_forall_compl_eq_zero hGout]
  apply (norm_setIntegral_le_of_norm_le_const_ae'
    (isCompact_closedBall (0 : Space n) 1).measure_lt_top
    (Filter.Eventually.of_forall hGin)).trans_eq
  dsimp only [V]
  ring

end Falconer

end OAI
