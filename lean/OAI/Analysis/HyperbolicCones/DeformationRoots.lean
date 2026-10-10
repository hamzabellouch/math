import OAI.Analysis.HyperbolicCones.DeformationBasic

namespace OAI

noncomputable section

open Set Polynomial

namespace Paper256

theorem intervalPolynomial_eval (a b x : ℝ) :
    (intervalPolynomial a b).eval x = (1 - x / a) * (1 + x / b) := by
  simp [intervalPolynomial, div_eq_mul_inv]
  ring

theorem intervalPolynomial_isRoot_iff (a b x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (intervalPolynomial a b).IsRoot x ↔ x = -b ∨ x = a := by
  rw [Polynomial.IsRoot, intervalPolynomial_eval, mul_eq_zero]
  constructor
  · rintro (h | h)
    · right
      field_simp at h
      linarith
    · left
      field_simp at h
      linarith
  · rintro (rfl | rfl) <;> simp [ha, hb]

theorem deformedPolynomial_root_set (a b η t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    {x : ℝ | (deformedPolynomial a b η t).IsRoot x} =
      {-b / timeScale η t, a / timeScale η t} := by
  rw [deformedPolynomial_scaled]
  ext x
  simp only [mem_ofPred_eq, intervalPolynomial_isRoot_iff _ _ _
    (div_ne_zero ha.ne' (timeScale_positive η t hη).ne')
    (div_ne_zero hb.ne' (timeScale_positive η t hη).ne'),
    mem_insert_iff, mem_singleton_iff, neg_div]

theorem deformedPolynomial_roots_compact (a b η t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    IsCompact {x : ℝ | (deformedPolynomial a b η t).IsRoot x} := by
  rw [deformedPolynomial_root_set a b η t ha hb hη]
  exact (Set.toFinite _).isCompact

theorem intervalPolynomial_derivative_eval (a b x : ℝ) :
    (intervalPolynomial a b).derivative.eval x =
      b⁻¹ - a⁻¹ - 2 * (a⁻¹ * b⁻¹) * x := by
  simp [intervalPolynomial, Polynomial.derivative_mul]
  ring

theorem intervalPolynomial_roots_simple (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : (intervalPolynomial a b).IsRoot x) :
    (intervalPolynomial a b).derivative.eval x ≠ 0 := by
  rw [intervalPolynomial_isRoot_iff a b x ha.ne' hb.ne'] at hx
  rcases hx with rfl | rfl <;> rw [intervalPolynomial_derivative_eval] <;>
    intro h <;> field_simp at h <;> nlinarith

theorem deformedPolynomial_roots_simple (a b η t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) (x : ℝ)
    (hx : (deformedPolynomial a b η t).IsRoot x) :
    (deformedPolynomial a b η t).derivative.eval x ≠ 0 := by
  rw [deformedPolynomial_scaled] at hx ⊢
  exact intervalPolynomial_roots_simple _ _ x
    (div_pos ha (timeScale_positive η t hη))
    (div_pos hb (timeScale_positive η t hη)) hx

theorem intervalPolynomial_radial_aeval (a b x : ℝ) (z : ℂ) :
    ((intervalPolynomial a b).comp (C x * X)).aeval z =
      (1 - (a⁻¹ : ℝ) * (x * z)) * (1 + (b⁻¹ : ℝ) * (x * z)) := by
  simp [intervalPolynomial]

theorem intervalPolynomial_real_zero (a b x : ℝ) (z : ℂ)
    (hz : ((intervalPolynomial a b).comp (C x * X)).aeval z = 0) :
    z.im = 0 := by
  rw [intervalPolynomial_radial_aeval, mul_eq_zero] at hz
  rcases hz with hz | hz
  · have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hre
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at him
    simp only [← mul_assoc] at hre him
    have hax : a⁻¹ * x ≠ 0 := by
      intro h
      simp [h] at hre
    exact (mul_eq_zero.mp (show (a⁻¹ * x) * z.im = 0 by nlinarith)).resolve_left hax
  · have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hre
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, zero_add, Complex.zero_im] at him
    simp only [← mul_assoc] at hre him
    have hbx : b⁻¹ * x ≠ 0 := by
      intro h
      simp [h] at hre
    exact (mul_eq_zero.mp (show (b⁻¹ * x) * z.im = 0 by nlinarith)).resolve_left hbx

theorem deformedPolynomial_real_zero (a b η t x : ℝ)
    (_ha : 0 < a) (_hb : 0 < b) (_hη : 0 < η) (z : ℂ)
    (hz : ((deformedPolynomial a b η t).comp (C x * X)).aeval z = 0) :
    z.im = 0 := by
  rw [deformedPolynomial_scaled] at hz
  exact intervalPolynomial_real_zero _ _ x z hz

end Paper256

end

end OAI
