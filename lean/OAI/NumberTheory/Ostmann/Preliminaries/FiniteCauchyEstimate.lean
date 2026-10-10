import OAI.NumberTheory.Ostmann.Characters.AdditiveFourier

namespace OAI

/-! # Coefficient bounds by finite Fourier inversion on a circle

For a finite polynomial, a sufficiently large root-of-unity grid recovers every
coefficient exactly. This supplies the Cauchy estimate used in Section 5.3,
including for finite-dimensional operator spaces, without a dimension factor.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def cyclicPolynomial {N : ℕ} [NeZero N]
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (c : ZMod N → E) (r : ℝ) (z : ZMod N) : E :=
  ∑ j, ZMod.stdAddChar (j * z) • ((r ^ j.val : ℝ) : ℂ) • c j

theorem cyclicPolynomial_eq_invDFT {N : ℕ} [NeZero N]
    {E : Type*} [AddCommGroup E] [Module ℂ E] (c : ZMod N → E) (r : ℝ) :
    cyclicPolynomial c r = (N : ℂ) •
      ZMod.dft.symm (fun j => ((r ^ j.val : ℝ) : ℂ) • c j) := by
  funext z
  simp only [Pi.smul_apply, ZMod.invDFT_apply, smul_smul, mul_inv_cancel₀ (NeZero.ne (N : ℂ)),
    one_smul, cyclicPolynomial]

theorem cyclicPolynomial_coefficient {N : ℕ} [NeZero N]
    {E : Type*} [AddCommGroup E] [Module ℂ E] (c : ZMod N → E) (r : ℝ) (j : ZMod N) :
    (N : ℂ)⁻¹ • ZMod.dft (cyclicPolynomial c r) j = ((r ^ j.val : ℝ) : ℂ) • c j := by
  rw [cyclicPolynomial_eq_invDFT, map_smul]
  simp only [LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_smul,
    ← mul_assoc, inv_mul_cancel₀ (NeZero.ne (N : ℂ)), one_mul]

theorem normalized_dft_norm_le {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ZMod N → E) (M : ℝ) (hM : ∀ z, ‖f z‖ ≤ M) (j : ZMod N) :
    ‖(N : ℂ)⁻¹ • ZMod.dft f j‖ ≤ M := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hd : ‖ZMod.dft f j‖ ≤ N * M := by
    rw [ZMod.dft_apply]
    calc
      _ ≤ ∑ z, ‖ZMod.stdAddChar (-(z * j)) • f z‖ := norm_sum_le _ _
      _ = ∑ z, ‖f z‖ := by simp only [norm_smul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]
      _ ≤ ∑ _z : ZMod N, M := Finset.sum_le_sum (fun z _ => hM z)
      _ = _ := by simp
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (N : ℝ)⁻¹ * (N * M) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = M := by rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]

theorem cyclicPolynomial_coefficient_norm_le {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ZMod N → E) (r M : ℝ) (hr : 0 < r)
    (hM : ∀ z, ‖cyclicPolynomial c r z‖ ≤ M) (j : ZMod N) :
    ‖c j‖ ≤ M / r ^ j.val := by
  have hh := normalized_dft_norm_le (cyclicPolynomial c r) M hM j
  rw [cyclicPolynomial_coefficient, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (pow_pos hr _)] at hh
  exact (le_div_iff₀ (pow_pos hr _)).mpr (by simpa only [mul_comm] using hh)

theorem cyclicPolynomial_two_coefficient_norm_le {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ZMod N → ZMod N → E) (r M : ℝ) (hr : 0 < r)
    (hM : ∀ z w, ‖cyclicPolynomial (fun i => cyclicPolynomial (c i) r w) r z‖ ≤ M)
    (i j : ZMod N) : ‖c i j‖ ≤ M / r ^ i.val / r ^ j.val := by
  apply cyclicPolynomial_coefficient_norm_le (c i) r (M / r ^ i.val) hr
  intro w
  exact cyclicPolynomial_coefficient_norm_le
    (fun i => cyclicPolynomial (c i) r w) r M hr (fun z => hM z w) i

end Ostmann

end OAI
