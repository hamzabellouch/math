import OAI.MeasureTheory.Falconer.Radial.RadialNonstationary
import OAI.MeasureTheory.Falconer.Shells.OriginalShellIntegral

namespace OAI

/-!
# Radial localization for the actual shell measure

The normalized radial shell integral is exactly the Fourier transform of
its fixed Schwartz cutoff. This identifies the oscillatory kernel in the
longitudinal discarded terms and gives arbitrary power decay, including
after integration against finite spatial and angular laws.
-/

namespace Falconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

theorem radial_shell_oscillator_fourier (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0) (v s : ℝ) :
    (∫ r, Complex.exp (Complex.I * (r*s : ℝ))
      ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) =
        (𝓕 φ) (-((2 : ℝ)^v)*s/(2*Real.pi)) := by
  let R : ℝ := (2 : ℝ)^v
  have hR : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
  rw [PlanarFalconer.sourceAngularShellMeasure_integral v hΨ hpos hzero]
  change R⁻¹ • (∫ r, Ψ (r/R) • Complex.exp (Complex.I * (r*s : ℝ))) = _
  have hscale := Measure.integral_comp_div
    (fun u : ℝ => Ψ u • Complex.exp (Complex.I * (R*u*s : ℝ))) R
  have he (r : ℝ) : R*(r/R)*s = r*s := by field_simp
  simp_rw [he] at hscale
  rw [hscale, abs_of_pos hR, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with u
  have hfreq : -2*Real.pi*u*(-R*s/(2*Real.pi)) = R*u*s := by
    field_simp
  change Ψ u • Complex.exp (Complex.I * (R*u*s : ℝ)) =
    Complex.exp ((-2*Real.pi*u*(-R*s/(2*Real.pi)) : ℝ) * Complex.I) • φ u
  rw [hfreq, hφ, Complex.real_smul, smul_eq_mul]
  ring_nf

theorem radial_shell_arbitrary_decay (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ v s : ℝ,
      2*Real.pi*R^α ≤ (2 : ℝ)^v*|s| →
      ‖∫ r, Complex.exp (Complex.I * (r*s : ℝ))
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ‖ ≤ C*R^(-T) := by
  obtain ⟨C,hC,hdecay⟩ := radial_nonstationary_arbitrary_power φ hα T
  refine ⟨C,hC,?_⟩
  intro R hR v s hfreq
  rw [radial_shell_oscillator_fourier φ Ψ hφ hΨ hpos hzero]
  apply hdecay R hR
  rw [abs_div, abs_mul, abs_neg, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _),
    abs_of_pos (by positivity : (0 : ℝ) < 2*Real.pi)]
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < 2*Real.pi)).mpr (by nlinarith)

/-- Integrating a discarded term loses only its amplitude bound and the
finite mass of the remaining variables. The phase gap is required only
where the amplitude is nonzero. -/
theorem radial_discarded_term_bound_uniform {X : Type*} [MeasurableSpace X]
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure X) [IsFiniteMeasure μ], ∀ R : ℝ, 1 ≤ R → ∀ v : ℝ,
      ∀ (A : X → ℂ) (s : X → ℝ) (B : ℝ), 0 ≤ B →
      (∀ x, ‖A x‖ ≤ B) →
      (∀ x, A x ≠ 0 → 2*Real.pi*R^α ≤ (2 : ℝ)^v*|s x|) →
      ‖∫ x, ∫ r, A x * Complex.exp (Complex.I * (r*s x : ℝ))
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ ∂μ‖ ≤
        (B*C*μ.real Set.univ)*R^(-T) := by
  obtain ⟨C,hC,hdecay⟩ := radial_shell_arbitrary_decay φ Ψ hφ hΨ hpos hzero hα T
  refine ⟨C,hC,?_⟩
  intro μ hμ R hR v A s B hB hAbound hgap
  have hpoint (x : X) :
      ‖∫ r, A x * Complex.exp (Complex.I * (r*s x : ℝ))
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ‖ ≤ B*(C*R^(-T)) := by
    rw [integral_const_mul, norm_mul]
    by_cases hx : A x = 0
    · rw [hx, norm_zero, zero_mul]
      positivity
    · exact mul_le_mul (hAbound x) (hdecay R hR v (s x) (hgap x hx))
        (norm_nonneg _) hB
  have hi := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hpoint)
  exact hi.trans_eq (by ring)


theorem radial_discarded_term_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ v : ℝ,
      ∀ (A : X → ℂ) (s : X → ℝ) (B : ℝ), 0 ≤ B →
      (∀ x, ‖A x‖ ≤ B) →
      (∀ x, A x ≠ 0 → 2*Real.pi*R^α ≤ (2 : ℝ)^v*|s x|) →
      ‖∫ x, ∫ r, A x * Complex.exp (Complex.I * (r*s x : ℝ))
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ ∂μ‖ ≤
        (B*C*μ.real Set.univ)*R^(-T) := by
  obtain ⟨C,hC,hbound⟩ := radial_discarded_term_bound_uniform (X := X) φ Ψ hφ hΨ hpos hzero hα T
  exact ⟨C,hC,hbound μ⟩

end Falconer

end OAI
