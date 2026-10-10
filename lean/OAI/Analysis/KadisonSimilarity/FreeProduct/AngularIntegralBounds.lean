import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralPolynomialMoments

namespace OAI

/-! Norm control for the normalized angular Fourier integrals used in
the spectral-arc construction. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

def angularIntegral (f : ℝ → ℂ) (l : ℤ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) • ∫ x in -Real.pi..Real.pi, f x * angularCharacter l x

theorem angularIntegral_const (c : ℂ) (l : ℤ) :
    angularIntegral (fun _ => c) l = c * angularPowerMoment 0 l := by
  simp only [angularIntegral, angularPowerMoment, pow_zero, one_mul,
    intervalIntegral.integral_const_mul, Complex.real_smul]
  ring

@[simp] theorem norm_angularCharacter (l : ℤ) (x : ℝ) :
    ‖angularCharacter l x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem angularIntegral_sub (f g : ℝ → ℂ) (l : ℤ)
    (hf : IntervalIntegrable (fun x => f x * angularCharacter l x)
      volume (-Real.pi) Real.pi)
    (hg : IntervalIntegrable (fun x => g x * angularCharacter l x)
      volume (-Real.pi) Real.pi) :
    angularIntegral (fun x => f x - g x) l = angularIntegral f l - angularIntegral g l := by
  simp only [angularIntegral, sub_mul]
  rw [intervalIntegral.integral_sub hf hg, smul_sub]

/-- Normalized angular integration is contractive for the uniform bound. -/
theorem angularIntegral_norm_le (f : ℝ → ℂ) (l : ℤ) {C : ℝ}
    (_hC : 0 ≤ C) (hf : ∀ x ∈ Set.Ioc (-Real.pi) Real.pi, ‖f x‖ ≤ C) :
    ‖angularIntegral f l‖ ≤ C := by
  have hb : ‖∫ x in -Real.pi..Real.pi, f x * angularCharacter l x‖ ≤
      C * (2 * Real.pi) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -Real.pi) (b := Real.pi) (C := C) (f := fun x => f x * angularCharacter l x) ?_
    · simpa only [sub_neg_eq_add, ← two_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] using h
    · intro x hx
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hx
      simpa only [norm_mul, norm_angularCharacter, mul_one] using hf x hx
  rw [angularIntegral, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (by positivity : 0 ≤ 2 * Real.pi))]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (C * (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C := by field_simp

theorem angularIntegral_continuous_sub_bound (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (l : ℤ) {C : ℝ}
    (hC : 0 ≤ C) (hfg : ∀ x ∈ Set.Ioc (-Real.pi) Real.pi, ‖f x - g x‖ ≤ C) :
    ‖angularIntegral f l - angularIntegral g l‖ ≤ C := by
  rw [← angularIntegral_sub f g l
    ((hf.mul (angularCharacter_continuous l)).intervalIntegrable _ _)
    ((hg.mul (angularCharacter_continuous l)).intervalIntegrable _ _)]
  exact angularIntegral_norm_le _ l hC hfg

end KadisonSimilarity

end

end OAI
