import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedMissingClass

namespace OAI

/-! Away from lambda, the literal frequency series is supported on the
two signed primary classes. This is a finite ramified selection rule. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

private lemma unit_ramified_primary_congruence (r : Fin 3) :
    (3:Eisenstein) ∣ omegaE^(r:ℕ)*(4+lambdaE*(r:ℕ))-1 := by
  fin_cases r
  · exact ⟨1,by norm_num⟩
  · refine ⟨omegaE-1,?_⟩
    norm_num only [Fin.val_one,pow_one,Nat.cast_one,mul_one]
    dsimp only [lambdaE]
    linear_combination 2*omegaE_quadratic
  · refine ⟨-1-2*omegaE,?_⟩
    norm_num only [Fin.val_ofNat,Nat.cast_ofNat]
    dsimp only [lambdaE]
    linear_combination (4*omegaE+2)*omegaE_quadratic

theorem cubicThetaEisensteinGaussCoefficient_primary_support
    (e : Eisensteinˣ) (h : Eisenstein)
    (hpos : ¬primary h) (hneg : ¬primary (-h)) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^2) h=0 := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  have hn : ¬(3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*h+
      2*(((0+2)%3:ℕ):Eisenstein)+lambdaE*(r:ℕ) := by
    intro hd
    norm_num only [Nat.reduceAdd,Nat.reduceMod,Nat.cast_ofNat] at hd
    have hm : (3:Eisenstein) ∣ -h+(e:Eisenstein)*(4+lambdaE*(r:ℕ)) := by
      have ht := dvd_mul_of_dvd_right hd (e:Eisenstein)
      convert ht using 1
      have hi : (e:Eisenstein)*((e⁻¹:Eisensteinˣ):Eisenstein)=1 := by simp
      linear_combination h*hi
    rcases hr with he | he
    · have hc : (3:Eisenstein) ∣ (e:Eisenstein)*(4+lambdaE*(r:ℕ))-1 := by
        rw [he]
        exact unit_ramified_primary_congruence r
      apply hpos
      change (3:Eisenstein) ∣ h-1
      convert dvd_add (dvd_neg.mpr hm) hc using 1
      ring
    · have hc : (3:Eisenstein) ∣ (e:Eisenstein)*(4+lambdaE*(r:ℕ))+1 := by
        rw [he]
        convert dvd_neg.mpr (unit_ramified_primary_congruence r) using 1
        ring
      apply hneg
      change (3:Eisenstein) ∣ -h-1
      convert dvd_sub hm hc using 1
      ring
  simpa only [pow_zero,one_mul,ite_eq_right hn] using
    cubicThetaEisensteinGaussCoefficient_all_ramified e r hr 0 h

theorem cubicThetaFrequencyDirichlet_primary_support {s : ℂ} (hs : 2<s.re)
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) (hpos : ¬primary h) (hneg : ¬primary (-h)) :
    cubicThetaFrequencyDirichlet h s=0 := by
  have hM : ∀ n : ℕ, 1 ≤ n → ¬lambdaE^n ∣ h := by
    intro n hn hd
    exact hh ((pow_one lambdaE ▸ pow_dvd_pow lambdaE hn).trans hd)
  rw [cubicThetaFrequencyDirichlet_primary_finite hs h 1 hM]
  have hz (e : Eisensteinˣ) :
      ∑ n ∈ Finset.range 1, cubicThetaRamifiedFactor e n s h*
        cubicThetaPrimaryFourierSeries e n s h=0 := by
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
      cubicThetaRamifiedFactor,cubicThetaEisensteinGaussCoefficient_primary_support e h hpos hneg,
      zero_mul]
  simp only [hz,tsum_zero]

end CubicFirstMoment

end

end OAI
