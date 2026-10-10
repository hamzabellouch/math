import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeDirichlet
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeShiftRows

namespace OAI

/-! Eliminate the two actual prime-free twists to obtain the unramified
three-frequency relation in the initial half-plane. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaFrequencyDirichlet_primeShift {p : Eisenstein}
    (hp : primaryPrime p) {s : ℂ} (hs : 2<s.re) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaFrequencyDirichlet (p*h) s=cubicThetaPrimeFreeDirichlet p s h 2+
      cubicThetaPrimeSecondFactor p s h*cubicThetaPrimeFreeDirichlet p s h 0 := by
  rw [cubicThetaFrequencyDirichlet_primePowers_iterated hp hs]
  rw [tsum_eq_sum (s:=Finset.range 3)]
  · simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    simp_rw [cubicThetaPrimePowerTerm_prime_zero hp,cubicThetaPrimePowerTerm_prime_one hp,
      cubicThetaPrimePowerTerm_prime_two hp s h hh]
    simp only [tsum_zero,add_zero,tsum_mul_left]
    rfl
  · intro n hn
    have hn3 : 3 ≤ n := by simpa only [Finset.mem_range,not_lt] using hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn3
    have hz (d : CubicThetaPrimeFreeDenominator p) :
        cubicThetaPrimePowerTerm p hp s (p*h) (3+k,d)=0 := by
      simpa only [add_comm 3 k] using cubicThetaPrimePowerTerm_prime_high hp s h hh k d
    simp only [hz,tsum_zero]

lemma cubicThetaPrimeFactors_product {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaPrimeFirstFactor p s h*cubicThetaPrimeSecondFactor p s h=
      (norm p:ℂ)^2*((norm p:ℂ)^(-s))^3 := by
  have hc : cubicSymbol p h*star (cubicSymbol p h)=1 := by
    rw [Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hp.1
      (hp.2.coprime_iff_not_dvd.mpr hh)]
    norm_num
  have hg : gauss p*star (gauss p)=1 := by
    rw [Complex.star_def,Complex.mul_conj',norm_gauss_of_squarefree hp.1 hp.2.squarefree]
    norm_num
  have hq : (Real.sqrt (norm p):ℂ)^2=(norm p:ℂ) := by
    exact_mod_cast Real.sq_sqrt (norm_nonneg p)
  unfold cubicThetaPrimeFirstFactor cubicThetaPrimeSecondFactor
  calc
    _ = (cubicSymbol p h*star (cubicSymbol p h))*(gauss p*star (gauss p))*
        (Real.sqrt (norm p):ℂ)^2*(norm p:ℂ)*((norm p:ℂ)^(-s))^3 := by ring
    _ = _ := by rw [hc,hg,hq]; ring

theorem cubicThetaFrequencyDirichlet_primeHecke {p : Eisenstein}
    (hp : primaryPrime p) {s : ℂ} (hs : 2<s.re) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaFrequencyDirichlet (p^3*h) s=
      (1+(norm p:ℂ)^3*((norm p:ℂ)^(-s))^3)*cubicThetaFrequencyDirichlet h s-
      cubicThetaPrimeFirstFactor p s h*cubicThetaFrequencyDirichlet (p*h) s := by
  rw [cubicThetaFrequencyDirichlet_cube_recurrence hp hs h hh,
    cubicThetaFrequencyDirichlet_primeShift hp hs h hh,
    cubicThetaFrequencyDirichlet_primeEulerStep hp hs h hh]
  have he := cubicThetaPrimeFactors_product hp s h hh
  linear_combination (cubicThetaPrimeFreeDirichlet p s h 0)*he

end CubicFirstMoment

end

end OAI
