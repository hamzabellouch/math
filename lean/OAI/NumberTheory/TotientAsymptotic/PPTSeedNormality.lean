import OAI.NumberTheory.TotientAsymptotic.PublishedNormality
import OAI.NumberTheory.TotientAsymptotic.BandComparison

namespace OAI

/-!
The fixed seed introduces no nonnormal prime factors in the rotated-fiber
branch of Ford's construction.  For a fixed prime, the interval part of
normality is eventually vacuous and the small-factor bound follows from
`B(S) → ∞`.  This is the elementary seed step in exclusion (vi), p. 27.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma ppt_normal_prime_of_small_shift {p : ℕ} {S : ℝ} (hp : p.Prime)
    (hpS : (p-1 : ℕ) ≤ S)
    (hΩ : ((p-1).primeFactorsList.length : ℝ) ≤ 2*B S) :
    IsNormalPrime S p := by
  refine ⟨hp, ?_, ?_⟩
  · have hc : omegaIn (p-1) 1 S ≤ (p-1).primeFactorsList.length :=
      List.length_filter_le _ _
    exact (Nat.cast_le.mpr hc).trans hΩ
  · intro U T hSU hUT hT
    exfalso
    linarith

lemma ppt_fixed_prime_eventually_normal {p : ℕ} (hp : p.Prime) :
    ∀ᶠ S : ℝ in atTop, IsNormalPrime S p := by
  filter_upwards [eventually_ge_atTop (((p-1 : ℕ) : ℝ)),
    B_tendsto.eventually (eventually_ge_atTop
      (((p-1).primeFactorsList.length : ℝ)/2))] with S hS hB
  exact ppt_normal_prime_of_small_shift hp hS (by linarith)

/-- All prime divisors of one fixed positive seed preimage are eventually
normal for the same parameter. -/
theorem ppt_seed_prime_factors_eventually_normal {c : ℕ} (hc : 0 < c) :
    ∀ᶠ S : ℝ in atTop, ∀ p : ℕ, p.Prime → p ∣ c → IsNormalPrime S p := by
  have he : ∀ᶠ S : ℝ in atTop, ∀ p ∈ c.primeFactors, IsNormalPrime S p :=
    (eventually_all_finset c.primeFactors).mpr (fun p hp =>
      ppt_fixed_prime_eventually_normal (Nat.prime_of_mem_primeFactors hp))
  filter_upwards [he] with S hS
  intro p hp hpc
  exact hS p (Nat.mem_primeFactors.mpr ⟨hp, hpc, hc.ne'⟩)

/-- Multiplying an already normal candidate by the fixed seed preserves
normality of every prime divisor, uniformly in the candidate. -/
theorem ppt_seed_products_eventually_normal {c : ℕ} (hc : 0 < c) :
    ∀ᶠ S : ℝ in atTop, ∀ n : ℕ,
      (∀ p : ℕ, p.Prime → p ∣ n → IsNormalPrime S p) →
      ∀ p : ℕ, p.Prime → p ∣ c*n → IsNormalPrime S p := by
  filter_upwards [ppt_seed_prime_factors_eventually_normal hc] with S hS
  intro n hn p hp hpn
  rcases hp.dvd_mul.mp hpn with hpc | hpn
  · exact hS p hp hpc
  · exact hn p hp hpn

end TotientAsymptotic

end

end OAI
