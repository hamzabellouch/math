import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedUnitValue

namespace OAI

/-! The explicit finite ramified factor for all six global units. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaUnit_signed_power (e : Eisensteinˣ) :
    ∃ r : Fin 3, (e:Eisenstein)=omegaE^(r:ℕ) ∨ (e:Eisenstein)=-(omegaE^(r:ℕ)) := by
  obtain ⟨r,hr⟩ := eisenstein_unit_eq_signed_omega e.isUnit
  refine ⟨⟨r%3,Nat.mod_lt _ (by norm_num)⟩,?_⟩
  simpa only [cube_pow_mod omegaE_cube] using hr

lemma cubicThetaNorm_lambda_pow (n : ℕ) : norm (lambdaE^n)=(3:ℝ)^n := by
  simp only [norm,Subalgebra.coe_pow,map_pow,lambdaE_coe,traceLambda_normSq]

lemma cubicThetaNorm_unit_lambda_pow (e : Eisensteinˣ) (n : ℕ) :
    norm ((e:Eisenstein)*lambdaE^n)=(3:ℝ)^n := by
  rw [norm_mul_eq,norm_of_isUnit e.isUnit,one_mul,cubicThetaNorm_lambda_pow]

theorem cubicThetaEisensteinGaussCoefficient_all_ramified
    (e : Eisensteinˣ) (r : Fin 3)
    (he : (e:Eisenstein)=omegaE^(r:ℕ) ∨ (e:Eisenstein)=-(omegaE^(r:ℕ)))
    (n : ℕ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)) (lambdaE^n*h)=
      (3:ℂ)^n*(if (3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*h+
          2*(((n+2)%3:ℕ):Eisenstein)+lambdaE*(r:ℕ) then
        9*residueFourierChar 9 (by norm_num)
          (Ideal.Quotient.mk (modulus 9) (-(((e⁻¹:Eisensteinˣ):Eisenstein))*h)) else 0) := by
  rw [cubicThetaEisensteinGaussCoefficient_unit_ramified_inflation,
    cubicThetaUnitRamifiedBase_value e (r:ℕ) ((n+2)%3) he,
    cubicThetaRamifiedUnitNineGauss_eq,cubicThetaNorm_lambda_pow]
  push_cast
  rfl

theorem cubicThetaRamifiedFactor_value (e : Eisensteinˣ) (r : Fin 3)
    (he : (e:Eisenstein)=omegaE^(r:ℕ) ∨ (e:Eisenstein)=-(omegaE^(r:ℕ)))
    (n : ℕ) (s : ℂ) (h : Eisenstein) :
    cubicThetaRamifiedFactor e n s (lambdaE^n*h)=
      ((3:ℂ)^n*(if (3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*h+
          2*(((n+2)%3:ℕ):Eisenstein)+lambdaE*(r:ℕ) then
        9*residueFourierChar 9 (by norm_num)
          (Ideal.Quotient.mk (modulus 9) (-(((e⁻¹:Eisensteinˣ):Eisenstein))*h)) else 0))*
        ((3:ℂ)^(n+2))^(-s) := by
  rw [cubicThetaRamifiedFactor,cubicThetaEisensteinGaussCoefficient_all_ramified e r he,
    cubicThetaNorm_unit_lambda_pow]
  push_cast
  rfl

end CubicFirstMoment

end

end OAI
