import OAI.NumberTheory.EgyptianFractions.SmallPrimeClass
import OAI.NumberTheory.EgyptianFractions.PrimePrefixSize

namespace OAI
noncomputable section

open Filter Topology
open scoped BigOperators

namespace Problem337.DivisorMoment

/-- The selected-prime-prefix form of the small class estimate. The prefix
crosses sqrt(Y) at a prime p whose logarithm is below 4 log(S); its size and
smoothness are conclusions, not additional hypotheses on the class. -/
theorem small_prime_selected_prefix_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ S : ℝ in atTop,
      ∀ (v R Y : ℝ), S / (2 * Real.log S) ≤ v →
      1 ≤ Y → v / 2 ≤ Real.log Y → ∀ (N : ℕ),
      ∀ (A : Finset ℕ) (w : ℕ → ℝ), A ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ A, w (N + h) ≤ Real.exp R) →
      (∀ h ∈ A, ∃ d p : ℕ, 0 < d ∧ 0 < p ∧ d ∣ N + h ∧
        (d : ℝ) ≤ Real.sqrt Y ∧ Real.sqrt Y < (d : ℝ) * p ∧
        (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ d → ℓ ≤ p) ∧
        Real.log (p : ℝ) < v ^ (15 / 16 : ℝ) ∧
        Real.log (p : ℝ) < 4 * Real.log S) →
      (∑ h ∈ A, w (N + h)) ≤
        2 * Y * Real.exp (-v / 50 + C * S ^ (2 / 5 : ℝ) + R) := by
  obtain ⟨C, hC, hsum⟩ := small_prime_class_shifted_sum_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [Problem337.PrimePrefixSize.eventually_uniform_prefix_large,
    eventually_ge_atTop (1 : ℝ)] with S hpre hS
  intro v R Y hv hY hYlog N A w hA hw hpfx
  have hS0 : 0 < S := by linarith
  have hY0 : 0 < Y := by linarith
  have hsqrt : Real.sqrt Y ≤ Y := Real.sqrt_le_self_iff.mpr (Or.inr hY)
  apply hsum S v R Y hS hY0.le N ⌈S ^ (4 : ℕ)⌉₊
    (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ S ^ (4 : ℕ))).le
    A w hA hw
  intro h hh
  obtain ⟨d, p, hd, hp, hdvd, hdY, hcross, hpf, hplarge, hplog⟩ := hpfx h hh
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hlarge : Real.exp (v / 5) < (d : ℝ) :=
    hpre v d p Y hv hdR hpR hY0 hYlog hcross hplarge
  have hpS : (p : ℝ) < S ^ (4 : ℕ) := by
    apply (Real.log_lt_log_iff hpR (pow_pos hS0 4)).mp
    simpa only [Real.log_pow, Nat.cast_ofNat] using hplog
  refine ⟨d, hd, hdY.trans hsqrt, hdvd, ?_, hlarge.le⟩
  apply Nat.mem_smoothNumbers.mpr
  refine ⟨hd.ne', ?_⟩
  intro ℓ hℓ
  apply Nat.lt_ceil.mpr
  have hℓp := hpf ℓ (Nat.prime_of_mem_primeFactorsList hℓ)
    (Nat.dvd_of_mem_primeFactorsList hℓ)
  have hℓpR : (ℓ : ℝ) ≤ p := by exact_mod_cast hℓp
  exact hℓpR.trans_lt hpS

end Problem337.DivisorMoment

end

end OAI
