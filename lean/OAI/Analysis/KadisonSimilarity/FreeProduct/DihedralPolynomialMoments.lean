import OAI.Analysis.KadisonSimilarity.FreeProduct.ArcFourier
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart

namespace OAI

/-! The Haar and reflection-coset moments determine all polynomial moments
of the real part of a dihedral rotation. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

section Algebra
variable {A : Type*} [CStarAlgebra A]

theorem realPart_mul_rotation (w : Aˣ) (hw : star (w : A) = (↑w⁻¹ : A)) (l : ℤ) :
    (realPart (w : A) : A) * (↑(w ^ l) : A) =
      (1 / 2 : ℝ) • ((↑(w ^ (l + 1)) : A) + (↑(w ^ (l - 1)) : A)) := by
  have hplus : (w : A) * (↑(w ^ l) : A) = (↑(w ^ (l + 1)) : A) := by
    have h : w * w ^ l = w ^ (l + 1) := by
      simpa only [zpow_one, add_comm] using (zpow_add w 1 l).symm
    exact congrArg (fun a : Aˣ => (a : A)) h
  have hminus : (↑w⁻¹ : A) * (↑(w ^ l) : A) = (↑(w ^ (l - 1)) : A) := by
    rw [← Units.val_mul, ← zpow_neg_one, ← zpow_add]
    congr 2
    omega
  rw [realPart_apply_coe, smul_mul_assoc, add_mul, hw, hplus, hminus]
  simp only [one_div]

theorem realPart_pow_mul_rotation (w : Aˣ) (hw : star (w : A) = (↑w⁻¹ : A))
    (n : ℕ) (l : ℤ) :
    (realPart (w : A) : A) ^ (n + 1) * (↑(w ^ l) : A) =
      (1 / 2 : ℝ) •
        ((realPart (w : A) : A) ^ n * (↑(w ^ (l + 1)) : A) +
          (realPart (w : A) : A) ^ n * (↑(w ^ (l - 1)) : A)) := by
  rw [pow_succ, mul_assoc, realPart_mul_rotation w hw l, mul_smul_comm, mul_add]

end Algebra

/-- Angular characters with the sign convention of `arcFourierIntegral`. -/
def angularCharacter (l : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (((l : ℝ) * x : ℝ) * Complex.I)

theorem angularCharacter_continuous (l : ℤ) : Continuous (angularCharacter l) := by
  unfold angularCharacter
  fun_prop

theorem cosine_mul_angularCharacter (l : ℤ) (x : ℝ) :
    (Real.cos x : ℂ) * angularCharacter l x =
      (1 / 2 : ℂ) * (angularCharacter (l + 1) x + angularCharacter (l - 1) x) := by
  have hp : angularCharacter (l + 1) x =
      angularCharacter l x * Complex.exp ((x : ℂ) * Complex.I) := by
    rw [angularCharacter, angularCharacter, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hm : angularCharacter (l - 1) x =
      angularCharacter l x * Complex.exp (-(x : ℂ) * Complex.I) := by
    rw [angularCharacter, angularCharacter, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hp, hm, ← mul_add, ← Complex.two_cos, ← Complex.ofReal_cos]
  ring

/-- Normalized angular moments of powers of the real coordinate. -/
def angularPowerMoment (n : ℕ) (l : ℤ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) • ∫ x in -Real.pi..Real.pi,
    (Real.cos x : ℂ) ^ n * angularCharacter l x

theorem angularPowerMoment_zero (l : ℤ) :
    angularPowerMoment 0 l = if l = 0 then 1 else 0 := by
  by_cases hl : l = 0
  · subst l
    simp [angularPowerMoment, angularCharacter]
    field_simp
    ring
  · simp only [angularPowerMoment, pow_zero, one_mul, angularCharacter]
    rw [integral_arc_exponential Real.pi l (by exact_mod_cast hl), Real.sin_int_mul_pi]
    simp [hl]

theorem angularPowerMoment_succ (n : ℕ) (l : ℤ) :
    angularPowerMoment (n + 1) l =
      (1 / 2 : ℝ) • (angularPowerMoment n (l + 1) + angularPowerMoment n (l - 1)) := by
  have hi (k : ℤ) : IntervalIntegrable
      (fun x : ℝ => (Real.cos x : ℂ) ^ n * angularCharacter k x)
      volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal.comp Real.continuous_cos).pow n |>.mul
      (angularCharacter_continuous k)
  have hpoint : (fun x : ℝ => (Real.cos x : ℂ) ^ (n + 1) * angularCharacter l x) =
      fun x => (1 / 2 : ℂ) * ((Real.cos x : ℂ) ^ n * angularCharacter (l + 1) x +
        (Real.cos x : ℂ) ^ n * angularCharacter (l - 1) x) := by
    funext x
    rw [pow_succ, mul_assoc, cosine_mul_angularCharacter]
    ring
  rw [angularPowerMoment, hpoint, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hi _) (hi _)]
  simp only [angularPowerMoment, Complex.real_smul]
  push_cast
  ring

section Moments
variable {A : Type*} [CStarAlgebra A]

/-- The Haar law supplies precisely the scalar angular moments of the
real part, including every shifted Fourier coefficient. -/
theorem trace_realPart_pow_rotation (τ : A →ₗ[ℂ] ℂ) (w : Aˣ)
    (hw : star (w : A) = (↑w⁻¹ : A))
    (hhaar : ∀ l : ℤ, τ (↑(w ^ l) : A) = if l = 0 then 1 else 0)
    (n : ℕ) (l : ℤ) :
    τ ((realPart (w : A) : A) ^ n * (↑(w ^ l) : A)) = angularPowerMoment n l := by
  induction n generalizing l with
  | zero => simpa only [pow_zero, one_mul, angularPowerMoment_zero] using hhaar l
  | succ n ih =>
    rw [realPart_pow_mul_rotation w hw n l, τ.map_smul_of_tower,
      map_add, ih, ih, angularPowerMoment_succ]

/-- Vanishing on the entire reflection coset propagates to every polynomial
in the real part. -/
theorem trace_realPart_pow_rotation_reflection (τ : A →ₗ[ℂ] ℂ) (w : Aˣ) (d : A)
    (hw : star (w : A) = (↑w⁻¹ : A))
    (hcoset : ∀ l : ℤ, τ ((↑(w ^ l) : A) * d) = 0) (n : ℕ) (l : ℤ) :
    τ (((realPart (w : A) : A) ^ n * (↑(w ^ l) : A)) * d) = 0 := by
  induction n generalizing l with
  | zero => simpa only [pow_zero, one_mul] using hcoset l
  | succ n ih =>
    rw [realPart_pow_mul_rotation w hw n l, smul_mul_assoc, add_mul,
      τ.map_smul_of_tower, map_add, ih, ih, add_zero, smul_zero]

theorem trace_realPart_polynomial_rotation (τ : A →ₗ[ℂ] ℂ) (w : Aˣ)
    (hw : star (w : A) = (↑w⁻¹ : A))
    (hhaar : ∀ l : ℤ, τ (↑(w ^ l) : A) = if l = 0 then 1 else 0)
    (p : Polynomial ℝ) (l : ℤ) :
    τ (Polynomial.aeval (realPart (w : A) : A) p * (↑(w ^ l) : A)) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ x in -Real.pi..Real.pi,
        ((p.eval (Real.cos x) : ℝ) : ℂ) * angularCharacter l x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hi (r : Polynomial ℝ) : IntervalIntegrable
        (fun x : ℝ => ((r.eval (Real.cos x) : ℝ) : ℂ) * angularCharacter l x)
        volume (-Real.pi) Real.pi := by
      apply Continuous.intervalIntegrable
      exact (Complex.continuous_ofReal.comp (r.continuous.comp Real.continuous_cos)).mul
        (angularCharacter_continuous l)
    simp only [map_add, add_mul, Polynomial.eval_add, Complex.ofReal_add]
    rw [hp, hq, intervalIntegral.integral_add (hi p) (hi q), smul_add]
  | monomial n r =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, smul_mul_assoc, τ.map_smul_of_tower,
      trace_realPart_pow_rotation τ w hw hhaar]
    simp only [Polynomial.eval_monomial, Complex.ofReal_mul, Complex.ofReal_pow,
      mul_assoc, angularPowerMoment]
    rw [intervalIntegral.integral_const_mul]
    simp only [Complex.real_smul]
    ring

theorem trace_realPart_polynomial_rotation_reflection (τ : A →ₗ[ℂ] ℂ)
    (w : Aˣ) (d : A) (hw : star (w : A) = (↑w⁻¹ : A))
    (hcoset : ∀ l : ℤ, τ ((↑(w ^ l) : A) * d) = 0)
    (p : Polynomial ℝ) (l : ℤ) :
    τ ((Polynomial.aeval (realPart (w : A) : A) p * (↑(w ^ l) : A)) * d) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_mul, hp, hq, add_zero]
  | monomial n r =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, smul_mul_assoc, smul_mul_assoc, τ.map_smul_of_tower,
      trace_realPart_pow_rotation_reflection τ w d hw hcoset, smul_zero]

end Moments
end KadisonSimilarity

end

end OAI
