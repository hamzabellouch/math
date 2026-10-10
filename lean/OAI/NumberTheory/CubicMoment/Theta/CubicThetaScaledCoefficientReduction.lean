import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoefficientPrimaryReduction

namespace OAI

/-! The exact primary-to-global reduction also preserves one common
scalar normalization of the nonconstant Fourier coefficients. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaScaledAgreement_lambda_cube (A : ℂ) {h : Eisenstein} (hh : h≠0)
    (he : cubicThetaNormalizedObservedCoefficient h=A*cubicThetaArithmeticCoefficient (-lambdaE*h)) :
    cubicThetaNormalizedObservedCoefficient (lambdaE^3*h)=
      A*cubicThetaArithmeticCoefficient (-lambdaE*(lambdaE^3*h)) := by
  rw [cubicThetaNormalizedObservedCoefficient_lambda_cube hh,he,
    show -lambdaE*(lambdaE^3*h)=lambdaE^3*(-lambdaE*h) by ring,
    cubicThetaArithmeticCoefficient_lambdaCube (show lambdaE∣-lambdaE*h from ⟨-h,by ring⟩)]
  ring

lemma cubicThetaScaledAgreement_lambda_cube_pow (A : ℂ) {h : Eisenstein} (hh : h≠0)
    (he : cubicThetaNormalizedObservedCoefficient h=A*cubicThetaArithmeticCoefficient (-lambdaE*h))
    (k : ℕ) :
    cubicThetaNormalizedObservedCoefficient (lambdaE^(3*k)*h)=
      A*cubicThetaArithmeticCoefficient (-lambdaE*(lambdaE^(3*k)*h)) := by
  induction k with
  | zero => simpa only [mul_zero,pow_zero,one_mul] using he
  | succ k ih =>
    have ht : lambdaE^(3*(k+1))*h=lambdaE^3*(lambdaE^(3*k)*h) := by
      rw [Nat.mul_add,pow_add]
      ring
    rw [ht]
    exact cubicThetaScaledAgreement_lambda_cube A
      (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hh) ih

theorem cubicThetaScaledCoefficientAgreement_primary (A : ℂ)
    (H : ∀ h : Eisenstein, primary h → cubicThetaNormalizedObservedCoefficient h=
      A*cubicThetaArithmeticCoefficient (-lambdaE*h)) :
    ∀ h : Eisenstein, h≠0 → cubicThetaNormalizedObservedCoefficient h=
      A*cubicThetaArithmeticCoefficient (-lambdaE*h) := by
  have H0 (h : Eisenstein) (hh : ¬lambdaE∣h) :
      cubicThetaNormalizedObservedCoefficient h=A*cubicThetaArithmeticCoefficient (-lambdaE*h) := by
    by_cases hp : primary h
    · exact H h hp
    by_cases hn : primary (-h)
    · have h0 : h≠0 := fun hz => hh (hz ▸ dvd_zero lambdaE)
      rw [←cubicThetaNormalizedObservedCoefficient_neg h0,H (-h) hn,
        show -lambdaE*(-h)=-(-lambdaE*h) by ring,cubicThetaArithmeticCoefficient_even]
    · rw [cubicThetaNormalizedObservedCoefficient_primary_support_eq hh hp hn,
        cubicThetaArithmeticCoefficient_signed_primary_support hh hp hn,mul_zero]
  have H2 (h : Eisenstein) (hh : ¬lambdaE∣h) :
      cubicThetaNormalizedObservedCoefficient (lambdaE^2*h)=
        A*cubicThetaArithmeticCoefficient (-lambdaE*(lambdaE^2*h)) := by
    obtain ⟨a,e,ha,he⟩ := cubicThetaPrimaryRepresentative hh
    rw [he,cubicThetaNormalizedObservedCoefficient_lambda_square_unit ha,
      cubicThetaArithmeticCoefficient_ramified_signed ha,H a ha]
    ring
  intro h hh
  obtain ⟨k,u,hu,he⟩ := WfDvdMonoid.max_power_factor hh lambdaE_prime.irreducible
  have hu0 : u≠0 := fun hz => by rw [hz,mul_zero] at he; exact hh he
  have hr : k%3=0 ∨ k%3=1 ∨ k%3=2 := by omega
  rw [he,show lambdaE^k*u=lambdaE^(3*(k/3))*(lambdaE^(k%3)*u) by
    rw [←mul_assoc,←pow_add]; congr 2; omega]
  apply cubicThetaScaledAgreement_lambda_cube_pow A
    (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hu0)
  rcases hr with hr | hr | hr
  · simpa only [hr,pow_zero,one_mul] using H0 u hu
  · simp only [hr,pow_one,cubicThetaNormalizedObservedCoefficient_lambda_missing hu,
      show -lambdaE*(lambdaE*u)=-(lambdaE^2*u) by ring,
      cubicThetaArithmeticCoefficient_even,cubicThetaArithmeticCoefficient_ramified_two hu,mul_zero]
  · simpa only [hr] using H2 u hu

end CubicFirstMoment

end

end OAI
