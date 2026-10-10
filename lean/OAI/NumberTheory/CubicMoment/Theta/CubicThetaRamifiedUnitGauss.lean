import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedNineGauss
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUnitCharacterFourier

namespace OAI

/-! The finite ramified sum with its unit character retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaUnitCharacter_power {a : Eisenstein} (ha : primary a) (r : ℕ) :
    (cubicSymbol a omegaE)^r=
      residueFourierChar 9 (by norm_num)
        (Ideal.Quotient.mk (modulus 9) (lambdaE*(r:Eisenstein)*(a-1))) := by
  obtain ⟨t,ht⟩ := ha
  have he : a=1+3*t := by linear_combination ht
  have hc : cubicSymbol a omegaE=cubicThetaUnitCharacter t := by rw [he]; rfl
  rw [hc,cubicThetaUnitCharacter_fourier]
  have hp : (residueFourierChar 3 (by norm_num)
      (Ideal.Quotient.mk (modulus 3) (lambdaE*t)))^r=
      residueFourierChar 3 (by norm_num)
        (Ideal.Quotient.mk (modulus 3) (lambdaE*(r:Eisenstein)*t)) := by
    rw [show lambdaE*(r:Eisenstein)*t=r • (lambdaE*t) by simp; ring,map_nsmul,
      AddChar.map_nsmul_eq_pow]
  rw [hp,show lambdaE*(r:Eisenstein)*(a-1)=3*((lambdaE*(r:Eisenstein))*t)
    by rw [ht]; ring]
  simpa only [mul_assoc] using (cubicThetaFourier_nine_triple (lambdaE*(r:Eisenstein)) t).symm

def cubicThetaRamifiedUnitNineGauss (j r : ℕ) (h : Eisenstein) : ℂ :=
  ∑' x : Residues (9:Eisenstein),
    cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 x)*
      (cubicSymbol (residueRepresentative 9 x) omegaE)^r*
        residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h*x)

theorem cubicThetaRamifiedUnitNineGauss_eq (j r : ℕ) (h : Eisenstein) :
    cubicThetaRamifiedUnitNineGauss j r h=
      if (3:Eisenstein) ∣ h+2*(j:Eisenstein)+lambdaE*(r:Eisenstein) then
        9*residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h)
      else 0 := by
  classical
  let ψ := residueFourierChar (9:Eisenstein) (by norm_num)
  let b : Eisenstein := 2*(j:Eisenstein)+lambdaE*(r:Eisenstein)
  have hx (x : Residues (9:Eisenstein)) :
      cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 x)*
        (cubicSymbol (residueRepresentative 9 x) omegaE)^r*
          ψ (Ideal.Quotient.mk (modulus 9) h*x)=
      ψ (Ideal.Quotient.mk (modulus 9) (-b))*
        (if primary (residueRepresentative 9 x) then
          ψ (Ideal.Quotient.mk (modulus 9) (h+b)*x) else 0) := by
    rw [cubicThetaEisensteinWeight_lambda_pow]
    by_cases hp : primary (residueRepresentative 9 x)
    · rw [ite_eq_left hp,ite_eq_left hp,cubicThetaRamifiedCharacter_power hp,
        cubicThetaUnitCharacter_power hp,← ψ.map_add_eq_mul,
        ← ψ.map_add_eq_mul,← ψ.map_add_eq_mul]
      congr 1
      have he : 2*(j:Eisenstein)*(residueRepresentative 9 x-1)+
          lambdaE*(r:Eisenstein)*(residueRepresentative 9 x-1)+h*residueRepresentative 9 x=
          -b+(h+b)*residueRepresentative 9 x := by dsimp only [b]; ring
      have hz := congrArg (Ideal.Quotient.mk (modulus (9:Eisenstein))) he
      simpa only [map_add,map_mul,map_sub,map_one,map_neg,residueRepresentative_spec] using hz
    · rw [ite_eq_right hp,ite_eq_right hp,zero_mul,zero_mul,mul_zero]
  unfold cubicThetaRamifiedUnitNineGauss
  change (∑' x : Residues (9:Eisenstein),
    cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 x)*
      (cubicSymbol (residueRepresentative 9 x) omegaE)^r*
        ψ (Ideal.Quotient.mk (modulus 9) h*x))=_
  simp_rw [hx]
  rw [tsum_mul_left,cubicThetaPrimaryNine_fourier]
  change ψ (Ideal.Quotient.mk (modulus 9) (-b))*
    (if (3:Eisenstein) ∣ h+b then 9*ψ (Ideal.Quotient.mk (modulus 9) (h+b)) else 0)=_
  have hb : h+b=h+2*(j:Eisenstein)+lambdaE*(r:Eisenstein) := by dsimp only [b]; ring
  rw [← hb]
  split_ifs
  · calc
      _ = 9*(ψ (Ideal.Quotient.mk (modulus 9) (-b))*
        ψ (Ideal.Quotient.mk (modulus 9) (h+b))) := by ring
      _ = _ := by
        rw [← ψ.map_add_eq_mul,← map_add]
        rw [show -b+(h+b)=h by ring]
  · ring

end CubicFirstMoment

end

end OAI
