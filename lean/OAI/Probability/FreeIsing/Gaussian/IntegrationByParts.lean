import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem hasDerivAt_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal m v)
      (-(x - m) / (v : ℝ) * gaussianPDFReal m v x) x := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h := (((((hasDerivAt_id x).sub_const m).pow 2).neg.div_const
    (2 * (v : ℝ))).exp).const_mul ((Real.sqrt (2 * Real.pi * v))⁻¹)
  convert! h using 1
  simp only [gaussianPDFReal, Pi.neg_apply, Pi.pow_apply, id_eq,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp

theorem integrable_gaussian_iff_density {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {f : ℝ → ℝ} :
    Integrable f (gaussianReal m v) ↔
      Integrable (fun x => gaussianPDFReal m v x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  simpa only [toReal_gaussianPDF, smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF m v)
      (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top)) (g := f))

theorem gaussian_integral_centered_mul_eq_variance_mul_deriv
    (m : ℝ) (v : ℝ≥0) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfi : Integrable f (gaussianReal m v))
    (hf'i : Integrable f' (gaussianReal m v))
    (hxfi : Integrable (fun x => (x - m) * f x) (gaussianReal m v)) :
    (∫ x, (x - m) * f x ∂gaussianReal m v) =
      (v : ℝ) * ∫ x, f' x ∂gaussianReal m v := by
  by_cases hv : v = 0
  · subst v
    simp
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have huf := (integrable_gaussian_iff_density hv).mp hfi
  have huf' := (integrable_gaussian_iff_density hv).mp hf'i
  have hxuf := (integrable_gaussian_iff_density hv).mp hxfi
  have hfirst : Integrable (fun x => f x *
      (-(x - m) / (v : ℝ) * gaussianPDFReal m v x)) := by
    convert hxuf.const_mul (-(v : ℝ)⁻¹) using 1
    ext x
    ring
  have hsecond : Integrable (fun x => f' x * gaussianPDFReal m v x) := by
    simpa only [mul_comm] using huf'
  have hproduct : Integrable (fun x => f x * gaussianPDFReal m v x) := by
    simpa only [mul_comm] using huf
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := gaussianPDFReal m v)
    (u' := f') (v' := fun x => -(x - m) / (v : ℝ) * gaussianPDFReal m v x)
    (fun x _ => hf x) (fun x _ => hasDerivAt_gaussianPDFReal m hv x)
    hfirst hsecond hproduct
  have hfun : (fun x => f x * (-(x - m) / (v : ℝ) * gaussianPDFReal m v x)) =
      (fun x => -(v : ℝ)⁻¹ * (gaussianPDFReal m v x * ((x - m) * f x))) := by
    funext x
    ring
  rw [hfun, integral_const_mul] at hibp
  simp_rw [mul_comm (f' _) (gaussianPDFReal m v _)] at hibp
  rw [integral_gaussianReal_eq_integral_smul hv,
    integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have hmul := congrArg (fun z : ℝ => -(v : ℝ) * z) hibp
  field_simp at hmul
  simpa only [mul_assoc] using hmul

theorem gaussian_integral_centered_mul_of_bounded
    (m : ℝ) (v : ℝ≥0) {f f' : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hbound : ∀ x, |f x| ≤ C)
    (hf'i : Integrable f' (gaussianReal m v)) :
    (∫ x, (x - m) * f x ∂gaussianReal m v) =
      (v : ℝ) * ∫ x, f' x ∂gaussianReal m v := by
  have hfm : AEStronglyMeasurable f (gaussianReal m v) :=
    (continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)).aestronglyMeasurable
  have hb : ∀ᵐ x ∂gaussianReal m v, ‖f x‖ ≤ C :=
    Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  have hfi := Integrable.of_bound hfm C hb
  have hxi : Integrable (fun x : ℝ => x - m) (gaussianReal m v) :=
    ((memLp_id_gaussianReal 1).integrable (by norm_num)).sub (integrable_const m)
  exact gaussian_integral_centered_mul_eq_variance_mul_deriv m v hf hfi hf'i
    (hxi.mul_bdd hfm hb)

theorem gaussian_integral_centered_mul_of_bounded_deriv
    (m : ℝ) (v : ℝ≥0) {f f' : ℝ → ℝ} {C D : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hbound : ∀ x, |f x| ≤ C) (hbound' : ∀ x, |f' x| ≤ D) :
    (∫ x, (x - m) * f x ∂gaussianReal m v) =
      (v : ℝ) * ∫ x, f' x ∂gaussianReal m v := by
  apply gaussian_integral_centered_mul_of_bounded m v hf hbound
  have heq : f' = deriv f := funext (fun x => (hf x).deriv.symm)
  have hfm : AEStronglyMeasurable f' (gaussianReal m v) := by
    rw [heq]
    exact aestronglyMeasurable_deriv f _
  exact Integrable.of_bound hfm D
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound' x))

theorem gaussian_integral_mul_affine_of_bounded_deriv
    (a b : ℝ) {f f' : ℝ → ℝ} {C D : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hbound : ∀ x, |f x| ≤ C) (hbound' : ∀ x, |f' x| ≤ D) :
    (∫ z, z * f (a + b * z) ∂gaussianReal 0 1) =
      b * ∫ z, f' (a + b * z) ∂gaussianReal 0 1 := by
  have hderiv (z : ℝ) : HasDerivAt (fun z => f (a + b * z))
      (b * f' (a + b * z)) z := by
    simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using (hf (a + b * z)).comp z
      (((hasDerivAt_id z).const_mul b).const_add a)
  have hb' (z : ℝ) : |b * f' (a + b * z)| ≤ |b| * D := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbound' _) (abs_nonneg b)
  have h := gaussian_integral_centered_mul_of_bounded_deriv 0 1 hderiv
    (fun z => hbound (a + b * z)) hb'
  simpa only [sub_zero, NNReal.coe_one, one_mul, integral_const_mul] using h

end Problem367

end

end OAI
