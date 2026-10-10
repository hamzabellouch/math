import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedDirichletCube
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedMissingClass

namespace OAI

/-! Only the middle of the three retained low rows can contribute to
the cubic step. Its coefficient is still the actual finite Gauss sum. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_ramified_two_row
    (e : Eisensteinˣ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^4) (lambdaE^3*h)=0 := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  have hn : ¬(3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE*h)+
      2*(((2+2)%3:ℕ):Eisenstein)+lambdaE*(r:ℕ) := by
    intro hd
    have h3 : lambdaE ∣ (3:Eisenstein) := by
      refine ⟨-lambdaE,?_⟩
      rw [mul_neg,← pow_two,lambdaE_sq]
      ring
    have hz : lambdaE ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE*h)+
        lambdaE*(r:ℕ) := ⟨-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+(r:ℕ),by ring⟩
    have ht : lambdaE ∣ (2:Eisenstein) := by
      convert dvd_sub (h3.trans hd) hz using 1
      norm_num
    exact lambdaE_prime.not_isUnit
      ((primary_coprime_lambda primary_neg_two).isRelPrime (dvd_neg.mpr ht) dvd_rfl)
  have he := cubicThetaEisensteinGaussCoefficient_all_ramified e r hr 2 (lambdaE*h)
  have hp : lambdaE^2*(lambdaE*h)=lambdaE^3*h := by ring
  simpa only [hp,ite_eq_right hn,mul_zero] using he

theorem cubicThetaRamifiedLowDirichlet_middle (s : ℂ) (h : Eisenstein) :
    cubicThetaRamifiedLowDirichlet s h=
      ∑' e : Eisensteinˣ,
        cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^3) (lambdaE^3*h)*
          (27:ℂ)^(-s)*cubicThetaPrimaryFourierSeries e 1 s h := by
  rw [cubicThetaRamifiedLowDirichlet_primary]
  apply tsum_congr
  intro e
  have hz0 : cubicThetaRamifiedFactor e 0 s (lambdaE^3*h)=0 := by
    unfold cubicThetaRamifiedFactor
    rw [show lambdaE^3*h=lambdaE*(lambdaE^2*h) by ring,
      cubicThetaEisensteinGaussCoefficient_ramified_zero_row,zero_mul]
  have hz2 : cubicThetaRamifiedFactor e 2 s (lambdaE^3*h)=0 := by
    unfold cubicThetaRamifiedFactor
    rw [cubicThetaEisensteinGaussCoefficient_ramified_two_row,zero_mul]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,hz0,hz2,
    zero_mul,add_zero]
  unfold cubicThetaRamifiedFactor
  rw [cubicThetaNorm_unit_lambda_pow]
  norm_num

end CubicFirstMoment

end

end OAI
