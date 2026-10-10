import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationRemote
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteReductionStep
import Mathlib.Data.Matrix.Basic

namespace OAI

/-! The four-coordinate off-block Sylvester equation. The outgoing two-plane
is kept intact, so no separation is required between its two eigenvalues. -/

namespace DefocusingNLS

abbrev SpectralRemoteIndex := Fin 2 × Fin 2

def spectralRemoteBlock (j : SpectralRemoteIndex) : Fin 3 :=
  if j.2 = 0 then 0 else if j.1 = 0 then 1 else 2

noncomputable def spectralRemoteBlockPart
    (B : Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) :
    Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ :=
  fun i j => if spectralRemoteBlock i = spectralRemoteBlock j then B i j else 0

noncomputable def spectralRemoteOffChange (r : ℝ) (lambda : SpectralRemoteIndex → ℂ)
    (B : Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) :
    Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ :=
  fun i j => if spectralRemoteBlock i = spectralRemoteBlock j then 0 else
    -(B i j)/((r : ℂ)^2*(lambda i-lambda j))

theorem spectralRemote_sylvester (r : ℝ) (hr : r ≠ 0)
    (lambda : SpectralRemoteIndex → ℂ) (B : Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ)
    (hgap : ∀ i j, spectralRemoteBlock i ≠ spectralRemoteBlock j → lambda i ≠ lambda j) :
    Matrix.diagonal (fun i => (r : ℂ)^2*lambda i)*spectralRemoteOffChange r lambda B-
      spectralRemoteOffChange r lambda B*Matrix.diagonal (fun i => (r : ℂ)^2*lambda i) =
        spectralRemoteBlockPart B-B := by
  ext i j
  simp only [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hij : spectralRemoteBlock i = spectralRemoteBlock j
  · simp only [spectralRemoteOffChange,spectralRemoteBlockPart,hij,ite_true,mul_zero,zero_mul,sub_self]
  · have hden : lambda i-lambda j ≠ 0 := sub_ne_zero.mpr (hgap i j hij)
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    simp only [spectralRemoteOffChange,spectralRemoteBlockPart,hij,ite_false,zero_sub]
    field_simp
    ring

theorem spectralRemote_off_change_bound (r gap : ℝ) (hr : 0 < r) (hgap : 0 < gap)
    (lambda : SpectralRemoteIndex → ℂ) (B : Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ)
    (hsep : ∀ i j, spectralRemoteBlock i ≠ spectralRemoteBlock j → gap ≤ ‖lambda i-lambda j‖)
    (i j : SpectralRemoteIndex) :
    ‖spectralRemoteOffChange r lambda B i j‖ ≤ ‖B i j‖/(r^2*gap) := by
  by_cases hij : spectralRemoteBlock i = spectralRemoteBlock j
  · simp only [spectralRemoteOffChange,hij,ite_true,norm_zero]
    positivity
  · simp only [spectralRemoteOffChange,hij,ite_false,norm_div,norm_neg,norm_mul,norm_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact div_le_div_of_nonneg_left (norm_nonneg _)
      (mul_pos (sq_pos_of_pos hr) hgap)
      (mul_le_mul_of_nonneg_left (hsep i j hij) (sq_nonneg r))

end DefocusingNLS

end OAI
