import OAI.NumberTheory.EgyptianFractions.PrimePowerFourierError

namespace OAI
noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace Problem337

/-- Removing higher prime powers from any bounded complex phase costs at most
exactly the elementary Chebyshev error. No distribution of primes is assumed. -/
theorem norm_mangoldt_sub_prime_phase_sum_le (N : ℕ) (w : ℕ → ℂ)
    (hw : ∀ n ∈ Finset.Icc 1 N, ‖w n‖ ≤ 1) :
    ‖(∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * w n) -
      ∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime, (Real.log (n : ℝ) : ℂ) * w n‖ ≤
      Chebyshev.psi N - Chebyshev.theta N := by
  classical
  have hprime :
      (∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime, (Real.log (n : ℝ) : ℂ) * w n) =
      ∑ n ∈ Finset.Icc 1 N, (primeLogWeight n : ℂ) * w n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime <;> simp [primeLogWeight, hp]
  rw [hprime]
  exact norm_mangoldt_sum_sub_prime_sum_le N w hw

/-- The prime-power discrepancy remains negligible after multiplying by any
fixed real power of the logarithm. -/
theorem primePowerError_mul_log_isLittleO (D : ℝ) :
    (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) * Real.log x ^ D)
      =o[atTop] (fun x : ℝ => x) := by
  have hlog := isLittleO_log_rpow_rpow_atTop D
    (by norm_num : (0 : ℝ) < 1 / 2)
  have h := Chebyshev.isBigO_psi_sub_theta_sqrt.mul_isLittleO hlog
  apply h.congr'
  · exact Eventually.of_forall (fun x => rfl)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    norm_num

/-- Uniform prime-power deletion with an arbitrary logarithmic saving. The
onset is independent of the complex phases. -/
theorem eventually_norm_mangoldt_sub_prime_phase_sum_le
    (D ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ w : ℕ → ℂ,
      (∀ n ∈ Finset.Icc 1 N, ‖w n‖ ≤ 1) →
      ‖(∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * w n) -
        ∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime, (Real.log (n : ℝ) : ℂ) * w n‖ ≤
        ε * (N : ℝ) / Real.log (N : ℝ) ^ D := by
  have hsmall := (primePowerError_mul_log_isLittleO D).bound hε
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall
  filter_upwards [hnat, eventually_ge_atTop (2 : ℕ)] with N hN hN2
  intro w hw
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hpow : 0 < Real.log (N : ℝ) ^ D := Real.rpow_pos_of_pos hlog D
  have herr : Chebyshev.psi N - Chebyshev.theta N ≤
      ε * (N : ℝ) / Real.log (N : ℝ) ^ D := by
    apply (le_div_iff₀ hpow).mpr
    rw [Real.norm_of_nonneg hNpos.le] at hN
    exact (le_abs_self _).trans hN
  exact (norm_mangoldt_sub_prime_phase_sum_le N w hw).trans herr

/-- Any upper bound for the Mangoldt phase sum transfers to the prime-only
logarithmically weighted sum with the explicit prime-power error. -/
theorem norm_prime_phase_sum_le_mangoldt_add_error (N : ℕ) (w : ℕ → ℂ)
    (hw : ∀ n ∈ Finset.Icc 1 N, ‖w n‖ ≤ 1) :
    ‖∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime, (Real.log (n : ℝ) : ℂ) * w n‖ ≤
      ‖∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * w n‖ +
        (Chebyshev.psi N - Chebyshev.theta N) := by
  have h := norm_mangoldt_sub_prime_phase_sum_le N w hw
  have ht := norm_add_le
    (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * w n)
    ((∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime, (Real.log (n : ℝ) : ℂ) * w n) -
      ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * w n)
  rw [add_sub_cancel, norm_sub_rev] at ht
  exact ht.trans (add_le_add_right h _)

/-- Uniform transfer of logarithmic minor-arc estimates. The set of allowed
phases may vary arbitrarily with the summation length. -/
theorem prime_phase_log_bound_of_mangoldt {ι : Type*}
    (w : ℕ → ι → ℕ → ℂ) (minor : ℕ → Set ι) (D ε : ℝ) (hε : 0 < ε)
    (hw : ∀ N t, t ∈ minor N → ∀ n ∈ Finset.Icc 1 N, ‖w N t n‖ ≤ 1)
    (hbound : ∀ᶠ N : ℕ in atTop, ∀ t ∈ minor N,
      ‖∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * w N t n‖ ≤
        (ε / 2) * (N : ℝ) / Real.log (N : ℝ) ^ D) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ minor N,
      ‖∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (Real.log (n : ℝ) : ℂ) * w N t n‖ ≤
        ε * (N : ℝ) / Real.log (N : ℝ) ^ D := by
  filter_upwards [hbound,
    eventually_norm_mangoldt_sub_prime_phase_sum_le D (ε / 2) (by positivity)]
      with N hN herr
  intro t ht
  have he := herr (w N t) (hw N t ht)
  have hb := hN t ht
  have htriangle := norm_add_le
    (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * w N t n)
    ((∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (Real.log (n : ℝ) : ℂ) * w N t n) -
      ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * w N t n)
  rw [add_sub_cancel, norm_sub_rev] at htriangle
  calc
    _ ≤ _ := htriangle
    _ ≤ (ε / 2) * (N : ℝ) / Real.log (N : ℝ) ^ D +
        (ε / 2) * (N : ℝ) / Real.log (N : ℝ) ^ D := add_le_add hb he
    _ = _ := by ring

end Problem337

end

end OAI
