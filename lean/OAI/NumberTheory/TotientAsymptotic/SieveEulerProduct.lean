import OAI.NumberTheory.TotientAsymptotic.ShiftedSieveDenominator
import OAI.NumberTheory.TotientAsymptotic.SmoothResidualMass
import OAI.NumberTheory.TotientAsymptotic.NormalPrimeBands

namespace OAI

/-! Elementary lower bounds for the sieve Euler product. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma primeEulerProduct_log_lower (N : ℕ) : Real.log N ≤ primeEulerProduct N := by
  have h := smooth_residual_reciprocal_mass N (Finset.Icc 1 N) (by
    intro n hn
    obtain ⟨hn1,hnN⟩ := Finset.mem_Icc.mp hn
    exact ⟨hn1,(largestPrimeFactor_le_self hn1).trans hnN⟩)
  have he : (∑ n ∈ Finset.Icc 1 N,(n:ℝ)⁻¹) = (harmonic N:ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  rw [he] at h
  have hl := log_le_harmonic_floor (N:ℝ) (Nat.cast_nonneg N)
  simp only [Nat.floor_natCast] at hl
  exact hl.trans h

lemma oddEulerProduct_eq (z : ℕ) (hz : 2 ≤ z) :
    primeEulerProduct z = 2 * ∏ p ∈ oddSievePrimes z,(p:ℝ)/(p-1) := by
  classical
  have htwo : 2 ∈ (Finset.Icc 2 z).filter Nat.Prime := by norm_num [hz]
  have hs : oddSievePrimes z = ((Finset.Icc 2 z).filter Nat.Prime).erase 2 := by
    ext p
    simp only [mem_oddSievePrimes,Finset.mem_erase,Finset.mem_filter,Finset.mem_Icc]
    constructor
    · rintro ⟨hpz,hpp,hp2⟩
      exact ⟨hp2,⟨hpp.two_le,hpz⟩,hpp⟩
    · rintro ⟨hp2,⟨_,hpz⟩,hpp⟩
      exact ⟨hpz,hpp,hp2⟩
  rw [hs,primeEulerProduct,← Finset.mul_prod_erase _ _ htwo]
  norm_num

lemma oddEulerProduct_log_lower (z : ℕ) (hz : 2 ≤ z) :
    Real.log z / 2 ≤ ∏ p ∈ oddSievePrimes z,(p:ℝ)/(p-1) := by
  have h := primeEulerProduct_log_lower z
  rw [oddEulerProduct_eq z hz] at h
  linarith

lemma shiftedSieveWeight_euler_factor (b p : ℕ) (hpp : p.Prime) (hp2 : p ≠ 2) :
    ((p:ℝ)/(p-1))^2 ≤
      (1+shiftedSieveWeight b p) * (if p ∣ b then (p:ℝ)/(p-1) else 1) := by
  have hpR : (2:ℝ) < p := by have := hpp.two_le; exact_mod_cast (by omega : 2<p)
  rw [shiftedSieveWeight,shiftedSieveDensity_prime b p hpp]
  split_ifs with hd
  · have hn : (p:ℝ)≠0 := by linarith
    have he : 1+(p:ℝ)⁻¹/(1-(p:ℝ)⁻¹) = (p:ℝ)/(p-1) := by
      field_simp [show (p:ℝ)-1≠0 by linarith]
      ring
    rw [he]
    exact le_of_eq (pow_two _)
  · have hn : (p:ℝ)-2>0 := by linarith
    have hn' : (p:ℝ)-1>0 := by linarith
    have he : 1+2/(p:ℝ)/(1-2/(p:ℝ)) = (p:ℝ)/(p-2) := by field_simp; ring
    rw [mul_one,he]
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hn') hn).mpr
    nlinarith

lemma sieve_exceptional_product_le_totient {b : ℕ} (hb : 0 < b) (z : ℕ) :
    (∏ p ∈ oddSievePrimes z,if p ∣ b then (p:ℝ)/(p-1) else 1) ≤ (b:ℝ)/b.totient := by
  classical
  rw [← Finset.prod_filter,totient_ratio_product hb]
  apply Finset.prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_oddSievePrimes.mp hp).2.1,hd,hb.ne'⟩
  · intro p hp
    have hpp := (mem_oddSievePrimes.mp (Finset.mem_filter.mp hp).1).2.1
    have hp1 : (1:ℝ)<p := by exact_mod_cast hpp.one_lt
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · intro p hp _
    have hp1 : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    apply (le_div_iff₀ (by linarith : (0:ℝ)<p-1)).mpr
    linarith

lemma shiftedSieveEulerProduct_lower {b : ℕ} (hb : 0 < b) (z : ℕ) (hz : 2 ≤ z) :
    (Real.log z)^2 / 4 ≤
      (∏ p ∈ oddSievePrimes z,(1+shiftedSieveWeight b p)) * ((b:ℝ)/b.totient) := by
  have hfactor : (∏ p ∈ oddSievePrimes z,(p:ℝ)/(p-1))^2 ≤
      (∏ p ∈ oddSievePrimes z,(1+shiftedSieveWeight b p)) *
        (∏ p ∈ oddSievePrimes z,if p ∣ b then (p:ℝ)/(p-1) else 1) := by
    rw [← Finset.prod_pow,← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro p hp
      positivity
    · intro p hp
      exact shiftedSieveWeight_euler_factor b p (mem_oddSievePrimes.mp hp).2.1
        (mem_oddSievePrimes.mp hp).2.2
  have hp : 0 ≤ ∏ p ∈ oddSievePrimes z,(1+shiftedSieveWeight b p) :=
    Finset.prod_nonneg (fun p hp => by have := shiftedSieveWeight_nonneg b hp; linarith)
  have he := mul_le_mul_of_nonneg_left (sieve_exceptional_product_le_totient hb z) hp
  have hl := oddEulerProduct_log_lower z hz
  have hlog : 0 ≤ Real.log z := Real.log_nonneg (by exact_mod_cast (show 1≤z by omega))
  nlinarith

end TotientAsymptotic

end

end OAI
