import OAI.Analysis.LipschitzHilbert.Fourier.SchwartzBandEnergy

namespace OAI

/-! Construct the actual primitive of an annular Schwartz packet. The
Fourier quotient is smooth because the packet vanishes near frequency zero. -/

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped FourierTransform Topology

namespace LipschitzHilbert

private theorem derivative_coefficient_ne_zero {ξ : ℝ} (hξ : ξ ≠ 0) :
    (2 * Real.pi * Complex.I * ξ : ℂ) ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hξ)

theorem exists_schwartz_band_primitive (f : SchwartzMap ℝ ℂ) {r R : ℝ}
    (hr : 0 < r) (hlow : ∀ ξ, |ξ| < r → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, R < |ξ| → 𝓕 f ξ = 0) :
    ∃ A : SchwartzMap ℝ ℂ,
      (∀ x, deriv A x = f x) ∧
      (∀ ξ, |ξ| < r → 𝓕 A ξ = 0) ∧
      (∀ ξ, R < |ξ| → 𝓕 A ξ = 0) := by
  let q := fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ : ℂ)⁻¹ * 𝓕 f ξ
  have hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q := by
    rw [contDiff_iff_contDiffAt]
    intro ξ
    by_cases hξ : ξ = 0
    · subst ξ
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hr) hr] with t ht
      dsimp only [q]
      rw [hlow t (abs_lt.mpr ht), mul_zero]
    · have hc : ContDiffAt ℝ (↑(⊤ : ℕ∞))
          (fun t : ℝ => (2 * Real.pi * Complex.I * t : ℂ)) ξ :=
        contDiffAt_const.mul Complex.ofRealCLM.contDiff.contDiffAt
      exact (hc.inv (derivative_coefficient_ne_zero hξ)).mul
        ((𝓕 f).smooth ⊤).contDiffAt
  have hcompact : HasCompactSupport q := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-R) R))
    intro ξ hξ
    have hRξ : R < |ξ| := by
      by_contra h
      exact hξ (abs_le.mp (le_of_not_gt h))
    dsimp only [q]
    rw [hhigh ξ hRξ, mul_zero]
  let Q : SchwartzMap ℝ ℂ := hcompact.toSchwartzMap hq
  let A : SchwartzMap ℝ ℂ := 𝓕⁻ Q
  have hAQ : 𝓕 A = Q := fourier_fourierInv_eq Q
  have hderiv : SchwartzMap.derivCLM ℂ ℂ A = f := by
    apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
    ext ξ
    change 𝓕 (SchwartzMap.derivCLM ℂ ℂ A) ξ = 𝓕 f ξ
    rw [schwartz_fourier_deriv, hAQ]
    change (2 * Real.pi * Complex.I * ξ : ℂ) *
      ((2 * Real.pi * Complex.I * ξ : ℂ)⁻¹ * 𝓕 f ξ) = 𝓕 f ξ
    by_cases hξ : ξ = 0
    · subst ξ
      rw [hlow 0 (by simpa using hr)]
      simp
    · rw [← mul_assoc, mul_inv_cancel₀ (derivative_coefficient_ne_zero hξ), one_mul]
  refine ⟨A, ?_, ?_, ?_⟩
  · intro x
    exact congrArg (fun F : SchwartzMap ℝ ℂ => F x) hderiv
  · intro ξ hξ
    rw [hAQ]
    change q ξ = 0
    simp only [q, hlow ξ hξ, mul_zero]
  · intro ξ hξ
    rw [hAQ]
    change q ξ = 0
    simp only [q, hhigh ξ hξ, mul_zero]

theorem schwartz_primitive_energy (A f : SchwartzMap ℝ ℂ) {r : ℝ} (hr : 0 < r)
    (hderiv : ∀ x, deriv A x = f x)
    (hband : ∀ ξ, |ξ| < r → 𝓕 A ξ = 0) :
    (∫ x, ‖A x‖ ^ 2) ≤ (2 * Real.pi * r)⁻¹ ^ 2 * ∫ x, ‖f x‖ ^ 2 := by
  have h := schwartz_band_derivative_lower A hr hband
  simp only [hderiv] at h
  have hc : 0 < (2 * Real.pi * r) ^ 2 := sq_pos_of_pos (by positivity)
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    (2 * Real.pi * r) ^ 2 * (∫ x, ‖A x‖ ^ 2) ≤ ∫ x, ‖f x‖ ^ 2 := h
    _ = (2 * Real.pi * r) ^ 2 *
        ((2 * Real.pi * r)⁻¹ ^ 2 * ∫ x, ‖f x‖ ^ 2) := by
      field_simp

end LipschitzHilbert

end

end OAI
