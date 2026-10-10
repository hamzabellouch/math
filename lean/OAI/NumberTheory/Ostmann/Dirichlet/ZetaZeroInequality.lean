import OAI.NumberTheory.Jacobsthal.Harmonic.CharacterPositivity
import OAI.NumberTheory.Ostmann.Dirichlet.LogDerivativeRight
import OAI.NumberTheory.Ostmann.Dirichlet.ZetaZeroPenalty

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet

lemma zeta_pole_real_le_one {s : ℂ} (ht : 1 ≤ |s.im|) : (1 / (s - 1)).re ≤ 1 := by
  have hn : 1 ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
    exact ht.trans h
  exact (Complex.re_le_norm _).trans (by
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith : 0 < ‖s - 1‖)).mpr hn)

theorem exists_zeta_zero_reciprocal_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ sigma beta t : ℝ,
      1 < sigma → sigma ≤ 2 → 7 / 8 ≤ beta → beta < 1 → 1 ≤ |t| →
      riemannZeta ((beta : ℂ) + (t : ℂ) * Complex.I) = 0 →
      4 / (sigma - beta) ≤ 3 / (sigma - 1) + K * Real.log (|t| + 6) := by
  obtain ⟨Cp, hCp, hpen⟩ := uniform_regularZeta_zero_penalty
  obtain ⟨Cu, hCu, hupper⟩ := exists_zeta_all_height_log_bound
  obtain ⟨Cz, hCz, hzeta⟩ := Erdos970.strongPnt_triv_bound_zeta
  refine ⟨3 * Cz + 4 * Cp + 2 * Cu + 5, by positivity, ?_⟩
  intro sigma beta t hs hs2 hb hb1 ht hzero
  have hbeta1 : (beta : ℂ) + (t : ℂ) * Complex.I ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.one_re] at hh
    linarith
  have hregzero : regularZeta ((beta : ℂ) + (t : ℂ) * Complex.I) = 0 := by
    rw [regularZeta_eq_mul hbeta1, hzero, mul_zero]
  have hp := hpen sigma beta t hs hs2 hb hb1 hregzero
  have hpole := zeta_pole_real_le_one
    (s := (sigma : ℂ) + (t : ℂ) * Complex.I) (by simpa using ht)
  have h1 : (-logDeriv riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I)).re ≤
      Cp * Real.log (|t| + 6) + 1 - 1 / (sigma - beta) := by
    rw [neg_logDeriv_zeta_pole_split (by simpa using hs), Complex.add_re]
    simp only [logDeriv_apply, neg_div] at hp ⊢
    linarith
  have h2 := hupper ((sigma : ℂ) + (2 * t : ℝ) * Complex.I)
    (by simpa using hs) (by simpa using hs2)
  have hpole2 := zeta_pole_real_le_one
    (s := (sigma : ℂ) + (2 * t : ℝ) * Complex.I) (by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
      rw [abs_mul]
      norm_num
      linarith)
  have hdouble := mul_le_mul_of_nonneg_left (zeta_height_double_le t) hCu.le
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at h2
  have h2' : (-logDeriv riemannZeta ((sigma : ℂ) + (2 * t : ℝ) * Complex.I)).re ≤
      2 * Cu * Real.log (|t| + 6) + 1 := by linarith
  have hz := hzeta sigma 0 hs
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hz
  have hz' := (Complex.re_le_norm (-deriv riemannZeta (sigma : ℂ) /
    riemannZeta (sigma : ℂ))).trans hz
  have hpos := character_log_derivative_positivity (1 : DirichletCharacter ℂ 1) sigma t hs
  simp only [one_pow, DirichletCharacter.LFunction_modOne_eq] at hpos
  simp only [logDeriv_apply, ← neg_div] at h1 h2'
  have hH := zeta_height_ge_one t
  have hCz' := mul_le_mul_of_nonneg_left hH hCz
  simp only [mul_one] at hCz'
  simp only [div_eq_mul_inv] at hpos h1 h2' hz' ⊢
  nlinarith only [hpos, h1, h2', hz', hCz', hH]

end Ostmann.Dirichlet

end OAI
