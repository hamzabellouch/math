import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedAllRows

namespace OAI

/-! The first missing ramified valuation class vanishes already in the
convergent Eisenstein series. The argument retains all six unit classes. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

private lemma lambda_dvd_three : lambdaE ∣ (3:Eisenstein) := by
  refine ⟨-lambdaE,?_⟩
  rw [mul_neg,← pow_two,lambdaE_sq]
  ring

private lemma lambda_not_dvd_four : ¬lambdaE ∣ (4:Eisenstein) := by
  intro hd
  have hp : primary (4:Eisenstein) := ⟨1,by ring⟩
  exact lambdaE_prime.not_isUnit ((primary_coprime_lambda hp).isRelPrime hd dvd_rfl)

theorem cubicThetaEisensteinGaussCoefficient_ramified_zero_row
    (e : Eisensteinˣ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^2) (lambdaE*h)=0 := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  have hn : ¬(3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE*h)+
      2*(((0+2)%3:ℕ):Eisenstein)+lambdaE*(r:ℕ) := by
    intro hd
    have hk := lambda_dvd_three.trans hd
    have hz : lambdaE ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE*h)+
        lambdaE*(r:ℕ) := ⟨-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+(r:ℕ),by ring⟩
    apply lambda_not_dvd_four
    convert dvd_sub hk hz using 1
    norm_num
  simpa only [pow_zero,one_mul,ite_eq_right hn,mul_zero] using
    cubicThetaEisensteinGaussCoefficient_all_ramified e r hr 0 (lambdaE*h)

theorem cubicThetaEisensteinGaussCoefficient_ramified_one_row
    (e : Eisensteinˣ) {h : Eisenstein} (hh : ¬lambdaE ∣ h) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^3) (lambdaE*h)=0 := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  have hn : ¬(3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*h+
      2*(((1+2)%3:ℕ):Eisenstein)+lambdaE*(r:ℕ) := by
    intro hd
    have hk := lambda_dvd_three.trans hd
    norm_num only [Nat.reduceAdd,Nat.reduceMod,Nat.cast_zero,mul_zero,add_zero] at hk
    have hz : lambdaE ∣ lambdaE*(r:ℕ) := dvd_mul_right _ _
    have hp : lambdaE ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*h := by
      simpa only [add_sub_cancel_right] using dvd_sub hk hz
    rcases hp with ⟨t,ht⟩
    apply hh
    refine ⟨-(e:Eisenstein)*t,?_⟩
    have hi : (e:Eisenstein)*((e⁻¹:Eisensteinˣ):Eisenstein)=1 := by simp
    linear_combination -(e:Eisenstein)*ht-h*hi
  simpa only [pow_one,ite_eq_right hn,mul_zero] using
    cubicThetaEisensteinGaussCoefficient_all_ramified e r hr 1 h

theorem cubicThetaFrequencyDirichlet_lambda_missing {s : ℂ} (hs : 2<s.re)
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) :
    cubicThetaFrequencyDirichlet (lambdaE*h) s=0 := by
  have hM : ∀ n : ℕ, 2 ≤ n → ¬lambdaE^n ∣ lambdaE*h := by
    intro n hn hd
    have hp : lambdaE^2 ∣ lambdaE*h := (pow_dvd_pow lambdaE hn).trans hd
    rw [pow_two,mul_dvd_mul_iff_left lambdaE_prime.ne_zero] at hp
    exact hh hp
  rw [cubicThetaFrequencyDirichlet_primary_finite hs (lambdaE*h) 2 hM]
  have hz (e : Eisensteinˣ) :
      ∑ n ∈ Finset.range 2, cubicThetaRamifiedFactor e n s (lambdaE*h)*
        cubicThetaPrimaryFourierSeries e n s (lambdaE*h)=0 := by
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
      cubicThetaRamifiedFactor,cubicThetaEisensteinGaussCoefficient_ramified_zero_row,
      cubicThetaEisensteinGaussCoefficient_ramified_one_row e hh,zero_mul,add_zero]
  simp only [hz,tsum_zero]

end CubicFirstMoment

end

end OAI
