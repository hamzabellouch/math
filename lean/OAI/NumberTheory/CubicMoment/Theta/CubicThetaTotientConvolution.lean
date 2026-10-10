import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTotientEuler
import OAI.NumberTheory.CubicMoment.Estimates.IdealDivisorPower

namespace OAI

/-! The normalized finite-ring totient as the actual ideal Möbius
convolution. This identifies its scattering Dirichlet series. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaNormInverse : EisensteinArithmeticFunction →+* EisensteinArithmeticFunction :=
  MvPowerSeries.rescale (fun p => (normNat (idealPrimeRepresentative p):ℝ)⁻¹)

lemma cubicThetaNormInverse_coeff (A : EisensteinArithmeticFunction) (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν (cubicThetaNormInverse A)=
      MvPowerSeries.coeff ν A/idealExponentNorm ν := by
  rw [cubicThetaNormInverse,MvPowerSeries.coeff_rescale]
  have he : ν.prod (fun p n => ((normNat (idealPrimeRepresentative p):ℝ)⁻¹)^n)=
      (idealExponentNorm ν)⁻¹ := by
    simp only [Finsupp.prod,inv_pow]
    rw [idealExponentNorm_eq_prod,Finset.prod_inv_distrib]
  rw [he]
  ring

lemma cubicThetaNormInverse_X (p : EisensteinIdealPrime) :
    cubicThetaNormInverse (MvPowerSeries.X p)=
      MvPowerSeries.monomial (Finsupp.single p 1) (normNat (idealPrimeRepresentative p):ℝ)⁻¹ := by
  ext ν
  rw [cubicThetaNormInverse_coeff,MvPowerSeries.X_def]
  by_cases hν : ν=Finsupp.single p 1
  · subst ν
    simp [idealExponentNorm_single]
  · simp [MvPowerSeries.coeff_monomial,hν]

private lemma totient_finite_product (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν (idealZeta*cubicThetaNormInverse (finiteIdealMoebius S))=
      ∏ p ∈ S, if ν p=0 then 1 else 1-(normNat (idealPrimeRepresentative p):ℝ)⁻¹ := by
  induction S using Finset.induction_on generalizing ν with
  | empty => simp [finiteIdealMoebius,idealZeta,MvPowerSeries.coeff_apply]
  | @insert p S hp ih =>
    have he : idealZeta*cubicThetaNormInverse (finiteIdealMoebius (insert p S))=
        (idealZeta*cubicThetaNormInverse (finiteIdealMoebius S))*
          (1-MvPowerSeries.monomial (Finsupp.single p 1)
            (normNat (idealPrimeRepresentative p):ℝ)⁻¹) := by
      rw [finiteIdealMoebius,Finset.prod_insert hp,map_mul,map_sub,map_one,cubicThetaNormInverse_X]
      unfold finiteIdealMoebius
      ring
    rw [he,mul_sub,mul_one,map_sub,MvPowerSeries.coeff_mul_monomial,ih,ih]
    simp only [Finsupp.single_le_iff]
    rw [Finset.prod_insert hp]
    have ht : (∏ q ∈ S, if (ν-Finsupp.single p 1 : EisensteinIdealExponent) q=0 then 1 else
        1-(normNat (idealPrimeRepresentative q):ℝ)⁻¹)=
      ∏ q ∈ S, if ν q=0 then 1 else 1-(normNat (idealPrimeRepresentative q):ℝ)⁻¹ := by
      apply Finset.prod_congr rfl
      intro q hq
      simp [Finsupp.tsub_apply,ne_of_mem_of_not_mem hq hp]
    rw [ht]
    by_cases hn : ν p=0
    · simp [hn]
    · rw [ite_eq_left (Nat.one_le_iff_ne_zero.mpr hn),ite_eq_right hn]
      ring

lemma cubicThetaTotient_moebius (ν : EisensteinIdealExponent) :
    (cubicThetaIdealTotient ν:ℝ)/idealExponentNorm ν=
      MvPowerSeries.coeff ν (idealZeta*cubicThetaNormInverse idealMoebiusSeries) := by
  have hf : MvPowerSeries.coeff ν (idealZeta*cubicThetaNormInverse idealMoebiusSeries)=
      MvPowerSeries.coeff ν (idealZeta*cubicThetaNormInverse (finiteIdealMoebius ν.support)) := by
    rw [MvPowerSeries.coeff_mul,MvPowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [cubicThetaNormInverse_coeff,cubicThetaNormInverse_coeff]
    congr 2
    apply coeff_idealMoebiusSeries_eq_finite
    have hle : p.2≤ν := by
      rw [←Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
      exact le_add_of_nonneg_left zero_le
    intro q hq
    apply Finsupp.mem_support_iff.mpr
    intro hzero
    have he := hle q
    rw [hzero] at he
    exact (Finsupp.mem_support_iff.mp hq) (Nat.eq_zero_of_le_zero he)
  rw [hf,totient_finite_product,cubicThetaIdealTotient_euler]
  have hN := (idealExponentNorm_pos ν).ne'
  rw [mul_div_cancel_left₀ _ hN]
  apply Finset.prod_congr rfl
  intro p hp
  simp [Finsupp.mem_support_iff.mp hp,one_div]

lemma cubicThetaTotient_divisor_sum (ν : EisensteinIdealExponent) :
    (cubicThetaIdealTotient ν:ℝ)/idealExponentNorm ν=
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        MvPowerSeries.coeff p.1 idealMoebiusSeries/idealExponentNorm p.1 := by
  rw [cubicThetaTotient_moebius,mul_comm,MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [cubicThetaNormInverse_coeff]
  simp [idealZeta,MvPowerSeries.coeff_apply]

end CubicFirstMoment

end

end OAI
