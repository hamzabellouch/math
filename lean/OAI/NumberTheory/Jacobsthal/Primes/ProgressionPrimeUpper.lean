import OAI.NumberTheory.Jacobsthal.Sieve.SieveScale

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosPrimeInputs.ProgressionPrimeUpper

open _root_.Finset
open NumberTheoryLean.LargePrimeDeletion
open SubsetPrimeSieve PrimeProductOmissions AffinePrimeSieve SieveScale

lemma reduced_coprime {z q p : ℕ} (hq : 0 < q) (hp : p ∈ reducedPrimes z q) : q.Coprime p := by
  obtain ⟨hpz,hpq⟩ := mem_sdiff.mp hp
  have hprime := (mem_cutoffPrimes.mp hpz).1
  apply (hprime.coprime_iff_not_dvd.mpr ?_).symm
  intro hd
  exact hpq (Nat.mem_primeFactors.mpr ⟨hprime,hd,Nat.ne_of_gt hq⟩)

lemma modulus_factor_ge_one {q : ℕ} (hq : 0 < q) : 1 ≤ (q:ℝ)/q.totient := by
  have ht : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (le_div_iff₀ ht).mpr
  simpa only [one_mul] using (show (q.totient:ℝ) ≤ q by exact_mod_cast Nat.totient_le q)

theorem progression_prime_upper : ∃ C J₀ : ℝ, 0 < C ∧ 1 < J₀ ∧
    ∀ (N : ℕ) (a : ℤ) (q : ℕ) (J : ℝ), J₀ ≤ J → 0 < q → |(N:ℝ)-J| ≤ 1 →
      ((primeIndices N a q).card:ℝ) ≤ C * J * ((q:ℝ)/q.totient) / Real.log J := by
  obtain ⟨K,u₀,hK,hu₀,hEuler⟩ := reduced_product_upper
  obtain ⟨J₀,hJ₀,hcut⟩ := cutoff_eventually_ge u₀
  have hα := exponent_pos
  refine ⟨2*K/exponent+6,J₀,by positivity,hJ₀,?_⟩
  intro N a q J hJ hq hNJ
  have hJ1 : 1 < J := hJ₀.trans_le hJ
  have hJ0 : 0 < J := by linarith
  have hlog := Real.log_pos hJ1
  let u := cutoff J
  have huBase : u₀ ≤ u := hcut J hJ
  have hu2 : 2 ≤ u := hu₀.trans huBase
  have hu0 : 0 ≤ u := by linarith
  let P := reducedPrimes ⌊u⌋₊ q
  let R : ℝ := (q:ℝ)/q.totient
  have hR : 1 ≤ R := modulus_factor_ge_one hq
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (mem_cutoffPrimes.mp (mem_sdiff.mp hp).1).1
  have hsize : ∀ p ∈ P, (p:ℝ) ≤ u := by
    intro p hp
    have hh := (mem_cutoffPrimes.mp (mem_sdiff.mp hp).1).2
    exact (show (p:ℝ) ≤ (⌊u⌋₊:ℝ) by exact_mod_cast hh).trans (Nat.floor_le hu0)
  have hcop : ∀ p ∈ P, q.Coprime p := fun p hp => reduced_coprime hq hp
  have hEpos := (euler_pos hP).le
  have hsieve := affine_sieve_error N a q u level J P hu2 (by norm_num [level]) hJ0.le hNJ hP hsize hcop
  have hpow : u ^ level = Real.sqrt J := cutoff_power hJ0.le
  rw [hpow] at hsieve
  have hexp : Real.exp (-level/96) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num [level])
  have hsurv : ((survivors N a q P).card:ℝ) ≤ 2*J*euler P + 2*Real.sqrt J := by
    have hh := (abs_le.mp hsieve).2
    have hm := mul_le_mul_of_nonneg_left hexp (mul_nonneg hJ0.le hEpos)
    nlinarith
  have hcount : ((primeIndices N a q).card:ℝ) ≤ 2*J*euler P + 3*Real.sqrt J := by
    have hh := prime_count_le_sifted_add N a q u P hq hu0 hP hsize
    have hu := cutoff_le_sqrt hJ1.le
    change u ≤ Real.sqrt J at hu
    linarith
  have hEuler' : euler P ≤ K*R/Real.log u := hEuler u huBase q hq
  have hmain : 2*J*euler P ≤ (2*K/exponent)*J*R/Real.log J := by
    calc
      _ ≤ 2*J*(K*R/Real.log u) := mul_le_mul_of_nonneg_left hEuler' (by positivity)
      _ = _ := by
        change 2*J*(K*R/Real.log (cutoff J)) = _
        rw [log_cutoff hJ0]
        field_simp
  have hsqrt : Real.sqrt J ≤ 2*J*R/Real.log J := by
    calc
      _ ≤ 2*J/Real.log J := sqrt_le_log_scale hJ1
      _ = (2*J/Real.log J)*1 := by ring
      _ ≤ (2*J/Real.log J)*R := mul_le_mul_of_nonneg_left hR (by positivity)
      _ = _ := by ring
  have herr : 3*Real.sqrt J ≤ 6*J*R/Real.log J := by
    calc
      _ ≤ 3*(2*J*R/Real.log J) := mul_le_mul_of_nonneg_left hsqrt (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ 2*J*euler P + 3*Real.sqrt J := hcount
    _ ≤ (2*K/exponent)*J*R/Real.log J + 6*J*R/Real.log J := add_le_add hmain herr
    _ = _ := by ring

end ErdosPrimeInputs.ProgressionPrimeUpper

end

end Erdos970

end OAI
