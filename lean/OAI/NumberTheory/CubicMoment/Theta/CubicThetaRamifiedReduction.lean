import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedCoefficientSupport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedPrimaryResidue

namespace OAI

/-! Reduce the literal coefficient identity to its two nonvanishing
ramified classes. The third class is zero by the proved ramified selection rule. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaNormalizedObservedCoefficient_lambda_cube_pow
    {h : Eisenstein} (hh : h≠0) (k : ℕ) :
    cubicThetaNormalizedObservedCoefficient (lambdaE^(3*k)*h)=
      (1/3:ℂ)^k*cubicThetaNormalizedObservedCoefficient h := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : lambdaE^(3*(k+1))*h=lambdaE^3*(lambdaE^(3*k)*h) := by
      rw [Nat.mul_add,pow_add]
      ring
    rw [he,cubicThetaNormalizedObservedCoefficient_lambda_cube
      (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hh),ih,pow_succ']
    ring

theorem cubicThetaCoefficientAgreement_lambda_cube_pow_iff
    {h : Eisenstein} (hh : h≠0) (k : ℕ) :
    (cubicThetaNormalizedObservedCoefficient (lambdaE^(3*k)*h)=
      cubicThetaArithmeticCoefficient (-lambdaE*(lambdaE^(3*k)*h))) ↔
    cubicThetaNormalizedObservedCoefficient h=cubicThetaArithmeticCoefficient (-lambdaE*h) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : lambdaE^(3*(k+1))*h=lambdaE^3*(lambdaE^(3*k)*h) := by
      rw [Nat.mul_add,pow_add]
      ring
    rw [he,cubicThetaCoefficientAgreement_lambdaCube_iff
      (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hh)]
    exact ih

theorem cubicThetaNormalizedObservedCoefficient_missing_class
    {h : Eisenstein} (hh : ¬lambdaE∣h) (k : ℕ) :
    cubicThetaNormalizedObservedCoefficient (lambdaE^(3*k+1)*h)=0 := by
  have h0 : h≠0 := fun he => hh (he ▸ dvd_zero lambdaE)
  rw [pow_add,pow_one,mul_assoc,cubicThetaNormalizedObservedCoefficient_lambda_cube_pow
    (mul_ne_zero lambdaE_prime.ne_zero h0),
    cubicThetaNormalizedObservedCoefficient_lambda_missing hh,mul_zero]

theorem cubicThetaCoefficientAgreement_missing_class
    {h : Eisenstein} (hh : ¬lambdaE∣h) (k : ℕ) :
    cubicThetaNormalizedObservedCoefficient (lambdaE^(3*k+1)*h)=
      cubicThetaArithmeticCoefficient (-lambdaE*(lambdaE^(3*k+1)*h)) := by
  have h0 : h≠0 := fun he => hh (he ▸ dvd_zero lambdaE)
  rw [pow_add,pow_one,mul_assoc]
  exact (cubicThetaCoefficientAgreement_lambda_cube_pow_iff
    (mul_ne_zero lambdaE_prime.ne_zero h0) k).mpr
      (cubicThetaNormalizedObservedCoefficient_lambda_missing_eq hh)

theorem cubicThetaCoefficientAgreement_ramified_reduction :
    (∀ h : Eisenstein, h≠0 → cubicThetaNormalizedObservedCoefficient h=
      cubicThetaArithmeticCoefficient (-lambdaE*h)) ↔
    (∀ h : Eisenstein, ¬lambdaE∣h → cubicThetaNormalizedObservedCoefficient h=
      cubicThetaArithmeticCoefficient (-lambdaE*h)) ∧
    (∀ h : Eisenstein, ¬lambdaE∣h → cubicThetaNormalizedObservedCoefficient (lambdaE^2*h)=
      cubicThetaArithmeticCoefficient (-lambdaE*(lambdaE^2*h))) := by
  constructor
  · intro H
    constructor
    · intro h hh
      exact H h (fun he => hh (he ▸ dvd_zero lambdaE))
    · intro h hh
      exact H _ (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero)
        (fun he => hh (he ▸ dvd_zero lambdaE)))
  · rintro ⟨H0,H2⟩ h hh
    obtain ⟨k,u,hu,he⟩ := WfDvdMonoid.max_power_factor hh lambdaE_prime.irreducible
    have hu0 : u≠0 := fun hz => by rw [hz,mul_zero] at he; exact hh he
    have hr : k%3=0 ∨ k%3=1 ∨ k%3=2 := by omega
    rw [he,show lambdaE^k*u=lambdaE^(3*(k/3))*(lambdaE^(k%3)*u) by
      rw [←mul_assoc,←pow_add]; congr 2; omega]
    apply (cubicThetaCoefficientAgreement_lambda_cube_pow_iff
      (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hu0) (k/3)).mpr
    rcases hr with hr | hr | hr
    · simpa only [hr,pow_zero,one_mul] using H0 u hu
    · simpa only [hr,pow_one] using
        cubicThetaNormalizedObservedCoefficient_lambda_missing_eq hu
    · simpa only [hr] using H2 u hu

end CubicFirstMoment

end

end OAI
