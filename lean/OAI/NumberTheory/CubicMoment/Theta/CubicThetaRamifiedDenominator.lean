import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedCubeRows
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeValuation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedCoordinates

namespace OAI

/-! Unique ramified coordinates for exactly the admissible Eisenstein
denominators. The exponent starts at two because the rows are divisible by
three. Global units are retained. -/
noncomputable section
namespace CubicFirstMoment

abbrev CubicThetaPrimaryPart := {a : Eisenstein // primary a}

def cubicThetaRamifiedDenominator
    (v : Eisensteinˣ × ℕ × CubicThetaPrimaryPart) : CubicThetaDenominator :=
  ⟨(v.1:Eisenstein)*lambdaE^(v.2.1+2)*v.2.2.val,by
    refine ⟨-(v.1:Eisenstein)*lambdaE^v.2.1*v.2.2.val,?_⟩
    rw [pow_add,lambdaE_sq]
    ring,
    mul_ne_zero (mul_ne_zero v.1.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero))
      (primary_ne_zero v.2.2.property)⟩

theorem cubicThetaRamifiedDenominator_bijective :
    Function.Bijective cubicThetaRamifiedDenominator := by
  constructor
  · intro v w he
    have h := congrArg Subtype.val he
    change (v.1:Eisenstein)*lambdaE^(v.2.1+2)*v.2.2.val=
      (w.1:Eisenstein)*lambdaE^(w.2.1+2)*w.2.2.val at h
    obtain ⟨hu,hk,ha⟩ := unit_ramified_primary_unique v.2.2.property w.2.2.property h
    exact Prod.ext hu (Prod.ext (by omega) (Subtype.ext ha))
  · intro c
    obtain ⟨u,k,a,ha,hc⟩ := unit_ramified_primary_decomposition c.property.2
    have hpow : lambdaE^2 ∣ c.val := by
      rw [lambdaE_sq]
      exact neg_dvd.mpr c.property.1
    have hm : emultiplicity lambdaE c.val=(k:ℕ∞) := by
      rw [hc,emultiplicity_mul lambdaE_prime,emultiplicity_mul lambdaE_prime,
        unit_lambda_emultiplicity,primary_lambda_emultiplicity ha,
        emultiplicity_pow_self_of_prime lambdaE_prime,zero_add,add_zero]
    have hk : 2 ≤ k := by
      have hle := le_emultiplicity_of_pow_dvd hpow
      rw [hm] at hle
      exact_mod_cast hle
    refine ⟨(u,k-2,⟨a,ha⟩),?_⟩
    apply Subtype.ext
    change (u:Eisenstein)*lambdaE^(k-2+2)*a=c.val
    rw [Nat.sub_add_cancel hk]
    exact hc.symm

def cubicThetaRamifiedDenominatorEquiv :
    (Eisensteinˣ × ℕ × CubicThetaPrimaryPart) ≃ CubicThetaDenominator :=
  Equiv.ofBijective _ cubicThetaRamifiedDenominator_bijective

end CubicFirstMoment

end

end OAI
