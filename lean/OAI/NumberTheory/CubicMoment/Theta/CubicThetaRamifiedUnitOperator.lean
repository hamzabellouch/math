import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedPhaseEigen
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedForcingPhase

namespace OAI

/-! Sign symmetry of the literal finite ramified operators. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaRamifiedFactor_neg_all (e : Eisensteinˣ) (n : ℕ) (h : Eisenstein) (s : ℂ) :
    cubicThetaRamifiedFactor e n s (-h)=cubicThetaRamifiedFactor (-e) n s h := by
  have h3 : (3:Eisenstein)∣(e:Eisenstein)*lambdaE^(n+2) := by
    refine ⟨-(e:Eisenstein)*lambdaE^n,?_⟩
    rw [pow_add,lambdaE_sq]
    ring
  have h0 : (e:Eisenstein)*lambdaE^(n+2)≠0 :=
    mul_ne_zero e.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero)
  have he := cubicThetaEisensteinGaussCoefficient_neg h3 h0 (-h)
  rw [neg_neg] at he
  unfold cubicThetaRamifiedFactor
  rw [cubicThetaNorm_unit_lambda_pow,cubicThetaNorm_unit_lambda_pow]
  rw [Units.val_neg,neg_mul,he]

def cubicThetaRamifiedUnitOperator (n : ℕ) (h : Eisenstein)
    (g : Eisensteinˣ → ℂ) (d : Eisensteinˣ) : ℂ :=
  ∑' e : Eisensteinˣ, cubicThetaRamifiedFactor e n (4/3) (lambdaE^2*(h*(d:Eisenstein)))*g (d*e)

lemma cubicThetaRamifiedUnitOperator_neg (n : ℕ) (h : Eisenstein)
    (g : Eisensteinˣ → ℂ) (d : Eisensteinˣ) :
    cubicThetaRamifiedUnitOperator n h g (-d)=cubicThetaRamifiedUnitOperator n h g d := by
  unfold cubicThetaRamifiedUnitOperator
  rw [←(Equiv.neg Eisensteinˣ).tsum_eq]
  apply tsum_congr
  intro e
  simp only [Equiv.neg_apply,Units.val_neg,neg_mul]
  rw [show lambdaE^2*(h*(-(d:Eisenstein)))=-(lambdaE^2*(h*(d:Eisenstein))) by ring,
    cubicThetaRamifiedFactor_neg_all,neg_neg]
  congr 1
  simp

lemma cubicThetaRamifiedUnitOperator_mul_right (n : ℕ) (h : Eisenstein)
    (g : Eisensteinˣ → ℂ) (a : ℂ) (d : Eisensteinˣ) :
    cubicThetaRamifiedUnitOperator n h (fun e => g e*a) d=
      cubicThetaRamifiedUnitOperator n h g d*a := by
  unfold cubicThetaRamifiedUnitOperator
  simp_rw [←mul_assoc]
  rw [tsum_mul_right]

lemma cubicThetaRamifiedUnitOperator_mul_left (n : ℕ) (h : Eisenstein)
    (g : Eisensteinˣ → ℂ) (a : ℂ) (d : Eisensteinˣ) :
    cubicThetaRamifiedUnitOperator n h (fun e => a*g e) d=
      a*cubicThetaRamifiedUnitOperator n h g d := by
  unfold cubicThetaRamifiedUnitOperator
  simp_rw [show ∀ e : Eisensteinˣ,
      cubicThetaRamifiedFactor e n (4/3) (lambdaE^2*(h*(d:Eisenstein)))*(a*g (d*e))=
      a*(cubicThetaRamifiedFactor e n (4/3) (lambdaE^2*(h*(d:Eisenstein)))*g (d*e)) from
    fun _ => by ring]
  rw [tsum_mul_left]

end CubicFirstMoment

end

end OAI
