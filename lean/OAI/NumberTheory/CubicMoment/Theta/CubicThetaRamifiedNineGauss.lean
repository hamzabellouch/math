import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryNineFourier

namespace OAI

/-! Exact evaluation of the finite ramified Gauss sum. The three
ramified character exponents select three distinct additive congruence
classes; this calculation is independent of residue identification. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaRamifiedCharacter_power {a : Eisenstein} (ha : primary a) (j : ℕ) :
    (cubicSymbol a lambdaE)^j=
      residueFourierChar 9 (by norm_num)
        (Ideal.Quotient.mk (modulus 9) (2*(j:Eisenstein)*(a-1))) := by
  obtain ⟨t,ht⟩ := ha
  have he : a=1+3*t := by linear_combination ht
  have hc : cubicSymbol a lambdaE=cubicThetaRamifiedCharacter t := by rw [he]; rfl
  rw [hc,cubicThetaRamifiedCharacter_fourier]
  have hp : (residueFourierChar 3 (by norm_num)
      (Ideal.Quotient.mk (modulus 3) (2*t)))^j=
      residueFourierChar 3 (by norm_num)
        (Ideal.Quotient.mk (modulus 3) (2*(j:Eisenstein)*t)) := by
    rw [show 2*(j:Eisenstein)*t=j • (2*t) by simp; ring,map_nsmul,
      AddChar.map_nsmul_eq_pow]
  rw [hp,show 2*(j:Eisenstein)*(a-1)=3*((2*(j:Eisenstein))*t) by rw [ht]; ring]
  simpa only [mul_assoc] using (cubicThetaFourier_nine_triple (2*(j:Eisenstein)) t).symm

def cubicThetaRamifiedNineGauss (j : ℕ) (h : Eisenstein) : ℂ :=
  ∑' x : Residues (9:Eisenstein),
    cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 x)*
      residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h*x)

theorem cubicThetaRamifiedNineGauss_eq (j : ℕ) (h : Eisenstein) :
    cubicThetaRamifiedNineGauss j h=
      if (3:Eisenstein) ∣ h+2*(j:Eisenstein) then
        9*residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h)
      else 0 := by
  classical
  let ψ := residueFourierChar (9:Eisenstein) (by norm_num)
  have hx (x : Residues (9:Eisenstein)) :
      cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 x)*
        ψ (Ideal.Quotient.mk (modulus 9) h*x)=
      ψ (Ideal.Quotient.mk (modulus 9) (-2*(j:Eisenstein)))*
        (if primary (residueRepresentative 9 x) then
          ψ (Ideal.Quotient.mk (modulus 9) (h+2*(j:Eisenstein))*x) else 0) := by
    rw [cubicThetaEisensteinWeight_lambda_pow]
    by_cases hp : primary (residueRepresentative 9 x)
    · rw [ite_eq_left hp,ite_eq_left hp,cubicThetaRamifiedCharacter_power hp,
        ← ψ.map_add_eq_mul,← ψ.map_add_eq_mul]
      congr 1
      have he : 2*(j:Eisenstein)*(residueRepresentative 9 x-1)+
          h*residueRepresentative 9 x=
          -2*(j:Eisenstein)+(h+2*(j:Eisenstein))*residueRepresentative 9 x := by ring
      have hz := congrArg (Ideal.Quotient.mk (modulus (9:Eisenstein))) he
      simpa only [map_add,map_mul,map_sub,map_one,map_neg,residueRepresentative_spec] using hz
    · rw [ite_eq_right hp,ite_eq_right hp,zero_mul,mul_zero]
  unfold cubicThetaRamifiedNineGauss
  change (∑' x : Residues (9:Eisenstein),
    cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 x)*
      ψ (Ideal.Quotient.mk (modulus 9) h*x))=_
  simp_rw [hx]
  rw [tsum_mul_left,cubicThetaPrimaryNine_fourier]
  split_ifs
  · change ψ (Ideal.Quotient.mk (modulus 9) (-2*(j:Eisenstein)))*
      (9*ψ (Ideal.Quotient.mk (modulus 9) (h+2*(j:Eisenstein))))=
      9*ψ (Ideal.Quotient.mk (modulus 9) h)
    calc
      _ = 9*(ψ (Ideal.Quotient.mk (modulus 9) (-2*(j:Eisenstein)))*
        ψ (Ideal.Quotient.mk (modulus 9) (h+2*(j:Eisenstein)))) := by ring
      _ = _ := by
        rw [← ψ.map_add_eq_mul,← map_add]
        rw [show -2*(j:Eisenstein)+(h+2*(j:Eisenstein))=h by ring]
  · ring

end CubicFirstMoment

end

end OAI
