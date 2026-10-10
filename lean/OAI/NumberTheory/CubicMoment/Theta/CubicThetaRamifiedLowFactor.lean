import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedMiddleValue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedLowContinuation

namespace OAI

/-! The exact low-row correction is one primary series times a finite
modulus-three Fourier trace. No value of its residue is assumed. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaRamifiedTrace (h : Eisenstein) : ℂ :=
  residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) h)+
    residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) (-h))

lemma cubicThetaPrimaryFourierSeries_neg_one (n : ℕ) (s : ℂ) (h : Eisenstein) :
    cubicThetaPrimaryFourierSeries (-1) n s h=cubicThetaPrimaryFourierSeries 1 n s h := by
  unfold cubicThetaPrimaryFourierSeries
  apply tsum_congr
  intro a
  unfold cubicThetaPrimaryFourierTerm
  simp only [Units.val_neg,Units.val_one,cubicSymbol_neg a.property]

theorem cubicThetaRamifiedLowDirichlet_factor (s : ℂ) (h : Eisenstein) :
    cubicThetaRamifiedLowDirichlet s h=
      cubicThetaRamifiedCubeFactor s*cubicThetaRamifiedTrace h*
        cubicThetaPrimaryFourierSeries 1 1 s h := by
  let : Finite Eisensteinˣ := Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)
  rw [cubicThetaRamifiedLowDirichlet_middle]
  have he (e : Eisensteinˣ) :
      cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^3) (lambdaE^3*h)*
          (27:ℂ)^(-s)*cubicThetaPrimaryFourierSeries e 1 s h=
      (if e=1 then (27*residueFourierChar 3 (by norm_num)
          (Ideal.Quotient.mk (modulus 3) h))*(27:ℂ)^(-s)*
          cubicThetaPrimaryFourierSeries 1 1 s h else 0)+
      (if e=-1 then (27*residueFourierChar 3 (by norm_num)
          (Ideal.Quotient.mk (modulus 3) (-h)))*(27:ℂ)^(-s)*
          cubicThetaPrimaryFourierSeries 1 1 s h else 0) := by
    rw [cubicThetaEisensteinGaussCoefficient_middle]
    by_cases hp : e=1
    · subst e
      norm_num
    · by_cases hn : e=-1
      · subst e
        simp only [ite_eq_right hp,ite_true,cubicThetaPrimaryFourierSeries_neg_one,zero_add]
      · simp only [ite_eq_right hp,ite_eq_right hn,zero_mul,add_zero]
  simp_rw [he]
  rw [Summable.tsum_add Summable.of_finite Summable.of_finite]
  simp only [tsum_ite_eq]
  unfold cubicThetaRamifiedCubeFactor cubicThetaRamifiedTrace
  ring

end CubicFirstMoment

end

end OAI
