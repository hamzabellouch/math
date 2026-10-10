import OAI.NumberTheory.TotientAsymptotic.FordLargePrimeCount

namespace OAI

/-! The lower interval-factor counts forced by Ford's actual ordered preimages. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma normal_large_prime_band_lower {n k U V : ℕ} (hn : 0 < n)
    {S : ℝ} (hSU : S ≤ U) (hUV : U ≤ V)
    (hcard : k ≤ (distinctPrimesAbove n V).card)
    (hnormal : ∀ p ∈ n.primeFactors,IsNormalPrime S p) :
    (k:ℝ)*(B V-B U-Real.sqrt (B S*B V)) ≤ (omegaIn n.totient U V:ℝ) := by
  let A := B V-B U-Real.sqrt (B S*B V)
  by_cases hA : 0 ≤ A
  · by_cases he : U=V
    · subst V
      dsimp [A] at hA ⊢
      have hs := Real.sqrt_nonneg (B S*B U)
      have ho : (0:ℝ) ≤ omegaIn n.totient U U := Nat.cast_nonneg _
      nlinarith [show (0:ℝ) ≤ k from Nat.cast_nonneg k]
    have hlarge (p : ℕ) (hp : p ∈ distinctPrimesAbove n V) : (V:ℝ) ≤ (p-1:ℕ) := by
      have hVp : V < p := by exact_mod_cast distinctPrimesAbove_large n V hp
      exact_mod_cast (show V ≤ p-1 by omega)
    have hb := normal_prime_totient_band_lower hn (distinctPrimesAbove n V)
      (distinctPrimesAbove_subset hn V) hSU (by exact_mod_cast (lt_of_le_of_ne hUV he))
      (fun p hp => hnormal p (distinctPrimesAbove_subset hn V hp)) hlarge
    have hc : (k:ℝ) ≤ (distinctPrimesAbove n V).card := Nat.cast_le.mpr hcard
    exact (mul_le_mul_of_nonneg_right hc hA).trans hb
  · have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
    have hω : (0:ℝ) ≤ omegaIn n.totient U V := Nat.cast_nonneg _
    exact (mul_nonpos_of_nonneg_of_nonpos hk (le_of_lt (lt_of_not_ge hA))).trans hω

lemma ford_normal_band_lower {n k U V : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hkn : k ≤ n.primeFactorsList.length) {S : ℝ}
    (hSU : S ≤ U) (hUV : U ≤ V) (hVp : V < fordPrime n (k-1))
    (hsq : SquarefreeAbove n V)
    (hnormal : ∀ p ∈ n.primeFactors,IsNormalPrime S p) :
    (k:ℝ)*(B V-B U-Real.sqrt (B S*B V)) ≤ (omegaIn n.totient U V:ℝ) := by
  apply normal_large_prime_band_lower hn hSU hUV _ hnormal
  exact ford_prefix_distinct_primes hn hk hkn (by exact_mod_cast hVp) hsq

lemma ford_normal_part_band_lower {n k U V : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hkn : k ≤ n.primeFactorsList.length) {S F : ℝ}
    (hSU : S ≤ U) (hUV : U ≤ V) (hVF : (V:ℝ) ≤ F) (hVp : V < fordPrime n (k-1))
    (hsq : SquarefreeAbove n V)
    (hnormal : ∀ p ∈ n.primeFactors,IsNormalPrime S p) :
    (k:ℝ)*(B V-B U-Real.sqrt (B S*B V)) ≤
      (omegaIn (partBetween n.totient S F) U V:ℝ) := by
  rw [omegaIn_partBetween n.totient hSU hVF]
  exact ford_normal_band_lower hn hk hkn hSU hUV hVp hsq hnormal

end TotientAsymptotic

end

end OAI
