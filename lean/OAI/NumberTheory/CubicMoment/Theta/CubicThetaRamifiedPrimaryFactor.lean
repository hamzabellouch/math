import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedFinite
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussFactor

namespace OAI

/-! Separate the primary part of every actual ramified row. Reciprocity
reduces its correction to one explicit finite character squared. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRamifiedPrimaryPhase (e : Eisensteinˣ) {u : Eisenstein}
    (hu : primary u) (n : ℕ) :
    cubicSymbol u (3*((e:Eisenstein)*lambdaE^(n+2)))*
        cubicSymbol u ((e:Eisenstein)*lambdaE^(n+2))=
      (cubicSymbol u (e:Eisenstein)*(cubicSymbol u lambdaE)^n)^2 := by
  rw [cubicSymbol_mul_upper hu,cubicSymbol_mul_upper hu,cubicSymbol_pow_upper hu,
    pow_add]
  have hthree := cubicSymbol_three_lambda hu
  rw [cubicSymbol_mul_upper hu] at hthree
  have hcube := cubicSymbol_cube_of_isCoprime hu lambdaE (primary_coprime_lambda hu)
  calc
    _ = (cubicSymbol u (e:Eisenstein)*(cubicSymbol u lambdaE)^n)^2*
      (cubicSymbol u 3*cubicSymbol u lambdaE)*(cubicSymbol u lambdaE)^3 := by ring
    _ = _ := by rw [hthree,hcube,mul_one,mul_one]

theorem cubicThetaEisensteinGaussCoefficient_ramified_primary (e : Eisensteinˣ)
    {u : Eisenstein} (hu : primary u) (n : ℕ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)*u) h=
      (cubicSymbol u (e:Eisenstein)*(cubicSymbol u lambdaE)^n)^2*
        cubicThetaSymbolFourier u (primary_ne_zero hu) h*
          cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)) h := by
  have hc : (3:Eisenstein) ∣ (e:Eisenstein)*lambdaE^(n+2) := by
    refine ⟨-(e:Eisenstein)*lambdaE^n,?_⟩
    rw [pow_add,lambdaE_sq]
    ring
  have hc0 : (e:Eisenstein)*lambdaE^(n+2)≠0 :=
    mul_ne_zero e.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero)
  have hunit : IsCoprime (e:Eisenstein) u := ⟨(e⁻¹:Eisensteinˣ),0,by simp⟩
  have hcu : IsCoprime ((e:Eisenstein)*lambdaE^(n+2)) u :=
    hunit.mul_left ((primary_coprime_lambda hu).symm.pow_left)
  rw [mul_comm ((e:Eisenstein)*lambdaE^(n+2)) u,
    cubicThetaEisensteinGaussCoefficient_factor hu hc hc0 hcu,
    cubicThetaRamifiedPrimaryPhase e hu]

end CubicFirstMoment

end

end OAI
