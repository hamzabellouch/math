import OAI.MathematicalPhysics.DefocusingNLS.Certificates.MatchingBoundary
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! # Positivity of the two-dimensional Hermitian boundary form -/

namespace DefocusingNLS

noncomputable def hermitianPairForm (a d : ℝ) (c u v : ℂ) : ℝ :=
  a * Complex.normSq u + 2 * (c * star u * v).re + d * Complex.normSq v

theorem hermitianPairForm_square (a d : ℝ) (c u v : ℂ) :
    a * hermitianPairForm a d c u v = Complex.normSq ((a : ℂ) * u + c * v) +
      (a * d - Complex.normSq c) * Complex.normSq v := by
  simp only [hermitianPairForm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The elementary two-dimensional positive-definiteness criterion. -/
theorem hermitianPairForm_pos (a d : ℝ) (c u v : ℂ) (ha : 0 < a)
    (hdet : 0 < a * d - Complex.normSq c) (huv : u ≠ 0 ∨ v ≠ 0) :
    0 < hermitianPairForm a d c u v := by
  by_cases hv : v = 0
  · have hu : u ≠ 0 := huv.resolve_right (not_not.mpr hv)
    simpa only [hermitianPairForm, hv, mul_zero, Complex.zero_re, Complex.normSq_zero,
      zero_mul, add_zero] using mul_pos ha (Complex.normSq_pos.mpr hu)
  · have hpos : 0 < a * hermitianPairForm a d c u v := by
      rw [hermitianPairForm_square]
      exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
        (mul_pos hdet (Complex.normSq_pos.mpr hv))
    exact pos_of_mul_pos_right hpos ha.le

/-- A positive determinant prevents the leading coefficient from crossing zero.
A single positive value therefore determines the sign on the whole line. -/
theorem positive_leading_coefficient_of_det (a d : ℝ → ℝ) (c : ℝ → ℂ)
    (ha : Continuous a) (hdet : ∀ t, 0 < a t * d t - Complex.normSq (c t))
    (t₀ : ℝ) (h₀ : 0 < a t₀) : ∀ t, 0 < a t := by
  intro t
  by_contra ht
  have ht' : a t ≤ 0 := le_of_not_gt ht
  obtain ⟨x, hx⟩ := intermediate_value_univ t t₀ ha ⟨ht', h₀.le⟩
  have h := hdet x
  rw [hx, zero_mul, zero_sub] at h
  linarith [Complex.normSq_nonneg (c x)]

theorem hermitianPairForm_pos_on_line (a d : ℝ → ℝ) (c : ℝ → ℂ)
    (ha : Continuous a) (hdet : ∀ t, 0 < a t * d t - Complex.normSq (c t))
    (t₀ : ℝ) (h₀ : 0 < a t₀) (t : ℝ) (u v : ℂ) (huv : u ≠ 0 ∨ v ≠ 0) :
    0 < hermitianPairForm (a t) (d t) (c t) u v :=
  hermitianPairForm_pos _ _ _ _ _
    (positive_leading_coefficient_of_det a d c ha hdet t₀ h₀ t) (hdet t) huv

end DefocusingNLS

end OAI
