import OAI.NumberTheory.JointDickman.Analysis.MellinEnergyTransfer
import Mathlib.Analysis.Real.Pi.Bounds

namespace OAI

/-! # Angular-frequency normalization for the published Dirichlet estimates -/
namespace JointDickman
open Finset MeasureTheory

/-- The convention used in the Dirichlet-polynomial mean-square estimates. -/
noncomputable def angularMellinPolynomial (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, (a n / (n : ℂ)) * Complex.exp (((-Real.log (n : ℝ) * t : ℝ) : ℂ) * Complex.I)

theorem mellinPolynomial_eq_angular (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    mellinPolynomial S a t = angularMellinPolynomial S a (2 * Real.pi * t) := by
  unfold mellinPolynomial angularMellinPolynomial
  apply sum_congr rfl
  intro n _
  congr 1
  unfold additivePhase
  congr 1
  push_cast
  ring

/-- Changing from angular to Fourier frequency preserves a linear spectral
bound, since the constant term is reduced by the factor `2*pi`. -/
theorem mellinPolynomial_energy_of_angular (S : Finset ℕ) (a : ℕ → ℂ)
    {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hbound : ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖angularMellinPolynomial S a t‖ ^ 2) ≤ A + B * T) :
    ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖mellinPolynomial S a t‖ ^ 2) ≤ A + B * T := by
  intro T hT
  have hp : 0 < 2 * Real.pi := by positivity
  have hp1 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hTp : 1 ≤ 2 * Real.pi * T := by nlinarith
  simp_rw [mellinPolynomial_eq_angular]
  rw [intervalIntegral.integral_comp_mul_left (f := fun t => ‖angularMellinPolynomial S a t‖ ^ 2) hp.ne']
  simp only [smul_eq_mul, mul_neg]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (A + B * (2 * Real.pi * T)) :=
      mul_le_mul_of_nonneg_left (hbound _ hTp) (inv_nonneg.mpr hp.le)
    _ = A / (2 * Real.pi) + B * T := by field_simp
    _ ≤ A + B * T := add_le_add (div_le_self hA hp1) le_rfl

theorem angularMellinPolynomial_consecutive (a : ℕ → ℂ) {K L N : ℕ}
    (hKL : K ≤ L) (hLN : L ≤ N) (t : ℝ) :
    angularMellinPolynomial (Ioc K N) a t =
      angularMellinPolynomial (Ioc K L) a t + angularMellinPolynomial (Ioc L N) a t := by
  unfold angularMellinPolynomial
  rw [← Ioc_union_Ioc_eq_Ioc hKL hLN, sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]

/-- Only two dyadic spectral bounds are needed for the entire coefficient
range used by the short-window transfer. -/
theorem mellinPolynomial_two_dyadic_energy (a : ℕ → ℂ) (N : ℕ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfirst : ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2 * N)) a t‖ ^ 2) ≤ A + B * T)
    (hsecond : ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc (2 * N) (4 * N)) a t‖ ^ 2) ≤ A + B * T) :
    ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖mellinPolynomial (Ioc N (4 * N)) a t‖ ^ 2) ≤ 4 * A + (4 * B) * T := by
  apply mellinPolynomial_energy_of_angular _ _ (by positivity) (by positivity)
  intro T hT
  have hc (S : Finset ℕ) : Continuous (angularMellinPolynomial S a) := by
    apply continuous_finsetSum
    intro n _
    exact continuous_const.mul (Complex.continuous_exp.comp
      (((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))).mul_const Complex.I))
  have hp (t : ℝ) : ‖angularMellinPolynomial (Ioc N (4 * N)) a t‖ ^ 2 ≤
      2 * ‖angularMellinPolynomial (Ioc N (2 * N)) a t‖ ^ 2 +
        2 * ‖angularMellinPolynomial (Ioc (2 * N) (4 * N)) a t‖ ^ 2 := by
    rw [angularMellinPolynomial_consecutive a (by omega : N ≤ 2 * N) (by omega : 2 * N ≤ 4 * N)]
    have hh := norm_add_le (angularMellinPolynomial (Ioc N (2 * N)) a t)
      (angularMellinPolynomial (Ioc (2 * N) (4 * N)) a t)
    nlinarith [norm_nonneg (angularMellinPolynomial (Ioc N (2 * N)) a t),
      norm_nonneg (angularMellinPolynomial (Ioc (2 * N) (4 * N)) a t),
      norm_nonneg (angularMellinPolynomial (Ioc N (2 * N)) a t + angularMellinPolynomial (Ioc (2 * N) (4 * N)) a t),
      sq_nonneg (‖angularMellinPolynomial (Ioc N (2 * N)) a t‖ -
        ‖angularMellinPolynomial (Ioc (2 * N) (4 * N)) a t‖)]
  have hI (S : Finset ℕ) : IntervalIntegrable
      (fun t => ‖angularMellinPolynomial S a t‖ ^ 2) volume (-T) T :=
    ((hc S).norm.pow 2).intervalIntegrable _ _
  have hi := intervalIntegral.integral_mono (by linarith : -T ≤ T)
    (hI _) (((hI _).const_mul 2).add ((hI _).const_mul 2)) hp
  rw [intervalIntegral.integral_add ((hI _).const_mul 2) ((hI _).const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  nlinarith [hfirst T hT, hsecond T hT]

end JointDickman

end OAI
