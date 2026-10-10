import OAI.NumberTheory.Ostmann.Characters.SparseResidueProjection

namespace OAI

/-! # The actual additive kernel of the sparse spectral projection -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def sparseAdditiveKernel {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (x : ZMod p) : ℂ :=
  (t : ℂ) * additiveFourier (fun b => if b ∈ E then 1 else 0) (-x)

theorem sparseAdditiveKernel_formula {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (x : ZMod p) :
    sparseAdditiveKernel E t x = (t : ℂ) / p * ∑ b ∈ E, ZMod.stdAddChar (b * x) := by
  simp only [sparseAdditiveKernel, additiveFourier_apply, mul_neg, neg_neg,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, div_eq_mul_inv,
    mul_assoc]

theorem sparseAdditiveKernel_fourier {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (a : ZMod p) :
    additiveFourier (sparseAdditiveKernel E t) a =
      (t : ℂ) * (p : ℂ)⁻¹ * (if a ∈ E then 1 else 0) := by
  change additiveFourier (fun x => (t : ℂ) *
    additiveFourier (fun b => if b ∈ E then 1 else 0) (-x)) a = _
  rw [additiveFourier_const_mul, additiveFourier_reflect,
    additiveFourier_twice, neg_neg, ← mul_assoc]

theorem sparseAdditiveKernel_real {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : ∀ b, -b ∈ E ↔ b ∈ E) (t : ℝ) (x : ZMod p) :
    (sparseAdditiveKernel E t x).im = 0 := by
  have hr : (densityFourierInverse (fun b => if b ∈ E then (1 : ℂ) else 0) x).im = 0 := by
    apply densityFourierInverse_real
    intro b
    by_cases hb : b ∈ E <;> simp [hb, hE b]
  have hp : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p))).ne'
  change ((Real.sqrt (p : ℝ) : ℂ) *
    additiveFourier (fun b => if b ∈ E then 1 else 0) (-x)).im = 0 at hr
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hr
  have hz := (mul_eq_zero.mp hr).resolve_left hp
  simp only [sparseAdditiveKernel, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, hz, mul_zero]

theorem sparseAdditiveKernel_norm_le {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (ht : 0 ≤ t) (x : ZMod p) :
    ‖sparseAdditiveKernel E t x‖ ≤ t / p * E.card := by
  rw [sparseAdditiveKernel_formula, norm_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ b ∈ E, ‖ZMod.stdAddChar (b * x)‖ := norm_sum_le _ _
    _ = _ := by simp [ZMod.stdAddChar_apply]

/-- The raw kernel matrix is precisely the scalar multiple of the projection;
no normalization or discarded frequency is hidden in the identification. -/
theorem sparseAdditiveKernel_action {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (f : ZMod p → ℂ) (x : ZMod p) :
    (∑ y, f y * sparseAdditiveKernel E t (x - y)) =
      (t : ℂ) * finiteSpectralProjection E f x := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hraw : (fun x => ∑ y, f y * sparseAdditiveKernel E t (x - y)) =
      fun x => (p : ℂ) * additiveConvolution f (sparseAdditiveKernel E t) x := by
    funext x
    simp only [additiveConvolution, ← mul_assoc, mul_inv_cancel₀ hp, one_mul]
  have hf : ∀ a, densityFourier (fun x => ∑ y, f y * sparseAdditiveKernel E t (x - y)) a =
      densityFourier (fun x => (t : ℂ) * finiteSpectralProjection E f x) a := by
    intro a
    rw [hraw, densityFourier, additiveFourier_const_mul, additiveFourier_convolution,
      sparseAdditiveKernel_fourier, densityFourier_const_mul, finiteSpectralProjection_fourier]
    by_cases ha : a ∈ E
    · simp only [ite_eq_left ha, mul_one, densityFourier]
      field_simp
    · simp only [ite_eq_right ha, mul_zero]
  have hfun := congrArg (fun g : ZMod p → ℂ => densityFourierInverse g x) (funext hf)
  simpa only [densityFourierInverse_fourier] using hfun

end Ostmann

end OAI
