import OAI.NumberTheory.TotientAsymptotic.PrimeBandProducts
import OAI.NumberTheory.TotientFibers.FiniteFiber

namespace OAI

/-! Normal prime divisors of a preimage force many factors in its totient bands. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma omegaIn_dvd {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b) (U V : ℝ) :
    omegaIn a U V ≤ omegaIn b U V := by
  obtain ⟨c,rfl⟩ := hab
  have hc : c ≠ 0 := by intro h; simp [h] at hb
  rw [omegaIn_mul ha.ne' hc]
  omega

lemma shifted_prime_product_dvd_totient {n : ℕ} (P : Finset ℕ)
    (hP : P ⊆ n.primeFactors) : (∏ p ∈ P,(p-1)) ∣ n.totient := by
  have hp : ∀ p ∈ P,p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hP hp)
  have hd : (∏ p ∈ P,p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset P n.primeFactors id hP).trans n.prod_primeFactors_dvd
  have hφ := Nat.totient_dvd_of_dvd hd
  rwa [TotientFibers.totient_prime_prod hp] at hφ

lemma normal_prime_totient_band_lower {n : ℕ} (hn : 0 < n) (P : Finset ℕ)
    (hP : P ⊆ n.primeFactors) {S U V : ℝ}
    (hSU : S ≤ U) (hUV : U < V)
    (hnormal : ∀ p ∈ P,IsNormalPrime S p)
    (hlarge : ∀ p ∈ P,V ≤ (p-1:ℕ)) :
    (P.card:ℝ)*(B V-B U-Real.sqrt (B S*B V)) ≤ (omegaIn n.totient U V:ℝ) := by
  have hp : ∀ p ∈ P,p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hP hp)
  have hpos : 0 < ∏ p ∈ P,(p-1) := Finset.prod_pos (fun p hmem => by have := (hp p hmem).two_le; omega)
  have hlower (p : ℕ) (hmem : p ∈ P) :
      B V-B U-Real.sqrt (B S*B V) ≤ (omegaIn (p-1) U V:ℝ) :=
    (normality_interval_bounds (hnormal p hmem) hSU hUV (hlarge p hmem) le_rfl).1
  have hs := Finset.sum_le_sum hlower
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hω := omegaIn_dvd hpos (Nat.totient_pos.mpr hn) (shifted_prime_product_dvd_totient P hP) U V
  have hωR : (omegaIn (∏ p ∈ P,(p-1)) U V:ℝ) ≤ (omegaIn n.totient U V:ℝ) := by exact_mod_cast hω
  rw [omegaIn_prod _ _ (fun p hmem => by have := (hp p hmem).two_le; omega),Nat.cast_sum] at hωR
  exact hs.trans hωR

lemma omegaIn_partBetween (n : ℕ) {S F U V : ℝ} (hSU : S ≤ U) (hVF : V ≤ F) :
    omegaIn (partBetween n S F) U V=omegaIn n U V := by
  have he := ((partBetween_factors n S F).filter
    (fun p : ℕ => decide (U < (p:ℝ) ∧ (p:ℝ) ≤ V))).length_eq
  have hf : (n.primeFactorsList.filter (fun p : ℕ => S < (p:ℝ) ∧ (p:ℝ) ≤ F)).filter
      (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V)=
      n.primeFactorsList.filter (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V) := by
    simp only [List.filter_filter]
    apply List.filter_congr
    intro p _
    by_cases h : U < (p:ℝ) ∧ (p:ℝ) ≤ V
    · simp [h,hSU.trans_lt h.1,h.2.trans hVF]
    · simp [h]
  simpa only [hf,omegaIn] using he.symm

lemma normal_prime_interval_part_lower {n : ℕ} (hn : 0 < n) (P : Finset ℕ)
    (hP : P ⊆ n.primeFactors) {S F U V : ℝ}
    (hSU : S ≤ U) (hUV : U < V) (hVF : V ≤ F)
    (hnormal : ∀ p ∈ P,IsNormalPrime S p)
    (hlarge : ∀ p ∈ P,V ≤ (p-1:ℕ)) :
    (P.card:ℝ)*(B V-B U-Real.sqrt (B S*B V)) ≤
      (omegaIn (partBetween n.totient S F) U V:ℝ) := by
  rw [omegaIn_partBetween n.totient hSU hVF]
  exact normal_prime_totient_band_lower hn P hP hSU hUV hnormal hlarge

end TotientAsymptotic

end

end OAI
