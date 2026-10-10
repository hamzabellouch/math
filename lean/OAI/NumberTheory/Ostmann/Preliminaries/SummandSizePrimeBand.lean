import OAI.NumberTheory.Ostmann.MainWithoutProgression
import OAI.NumberTheory.Ostmann.ZeroDensity.ProgressionPrincipalPNT

namespace OAI

/-! # Elementary dyadic prime counts used in the summand-size argument -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

 theorem actual_theta_relative_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ ε * x := by
  let P := actualProgressionInput
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 P.decay P.decay_pos).comp
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  simp only [Real.rpow_zero, one_mul, Function.comp_def] at ht
  have hCt := ht.const_mul P.errorConstant
  rw [mul_zero] at hCt
  have hsmall := hCt.eventually_lt_const hε
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with x he hx
  have hbound := P.principal_theta_bound x hx
  have hm := mul_le_mul_of_nonneg_right he.le (by linarith : 0 ≤ x)
  nlinarith

noncomputable def sizePrimeBand (Q : ℕ) : Finset ℕ := Nat.primesLE (2 * Q) \ Nat.primesLE Q

 theorem mem_sizePrimeBand {Q p : ℕ} :
    p ∈ sizePrimeBand Q ↔ p.Prime ∧ Q < p ∧ p ≤ 2 * Q := by
  simp only [sizePrimeBand, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hle, hp⟩, hnot⟩
    have hn : ¬ p ≤ Q := fun hh => hnot ⟨hh, hp⟩
    exact ⟨hp, by omega, hle⟩
  · rintro ⟨hp, hlo, hhi⟩
    exact ⟨⟨hhi, hp⟩, by omega⟩

 theorem sizePrimeBand_log_sum (Q : ℕ) :
    (∑ p ∈ sizePrimeBand Q, Real.log (p : ℝ)) =
      Chebyshev.theta (2 * Q : ℕ) - Chebyshev.theta Q := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  have hsub : Nat.primesLE Q ⊆ Nat.primesLE (2 * Q) := by
    intro p hp
    obtain ⟨hpQ, hpprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩
  simpa only [sizePrimeBand] using
    eq_sub_of_add_eq (Finset.sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ)) hsub)

 theorem sizePrimeBand_eventual_bounds :
    ∀ᶠ Q : ℕ in atTop, 2 ≤ Q ∧
      (Q : ℝ) / (4 * Real.log (2 * Q)) ≤ (sizePrimeBand Q).card ∧
      (∑ p ∈ sizePrimeBand Q, Real.log (p : ℝ)) ≤ 3 * Q := by
  have ht := actual_theta_relative_small (by norm_num : (0 : ℝ) < 1 / 4)
  have htN := tendsto_natCast_atTop_atTop.eventually ht
  obtain ⟨N, hN⟩ := eventually_atTop.mp htN
  filter_upwards [eventually_ge_atTop (max N 2)] with Q hQ
  have hQ2 : 2 ≤ Q := (le_max_right _ _).trans hQ
  have hQN : N ≤ Q := (le_max_left _ _).trans hQ
  have hQp : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have h1 := hN Q hQN
  have h2 := hN (2 * Q) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h2
  have hmass : (Q : ℝ) / 4 ≤ ∑ p ∈ sizePrimeBand Q, Real.log (p : ℝ) := by
    rw [sizePrimeBand_log_sum]
    push_cast
    rw [abs_le] at h1 h2
    nlinarith
  have hupper : (∑ p ∈ sizePrimeBand Q, Real.log (p : ℝ)) ≤ 3 * Q := by
    rw [sizePrimeBand_log_sum]
    push_cast
    rw [abs_le] at h1 h2
    nlinarith
  have hcount : (∑ p ∈ sizePrimeBand Q, Real.log (p : ℝ)) ≤
      (sizePrimeBand Q).card * Real.log (2 * Q) := by
    calc
      _ ≤ ∑ _p ∈ sizePrimeBand Q, Real.log (2 * (Q : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hmem := mem_sizePrimeBand.mp hp
        exact Real.log_le_log (by exact_mod_cast hmem.1.pos) (by exact_mod_cast hmem.2.2)
      _ = _ := by simp
  have hl : 0 < Real.log (2 * (Q : ℝ)) := Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * Q))
  refine ⟨hQ2, ?_, hupper⟩
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.log (2 * (Q : ℝ)))).mpr
  nlinarith

end Ostmann

end OAI
