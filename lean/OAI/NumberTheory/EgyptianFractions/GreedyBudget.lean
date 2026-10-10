import Mathlib

namespace OAI
noncomputable section

namespace Problem337

/-- A natural greedy step budget logarithmic in `S`, sufficient for a target
unreduced denominator `exp (D*S)`. -/
theorem exists_logarithmic_greedy_budget (D S : ℝ)
    (hS : Real.exp 1 ≤ S) (hDS : D ≤ S * Real.log 2) :
    ∃ N : ℕ,
      ((N + 1 : ℕ) : ℝ) ≤ (2 / Real.log 2 + 2) * Real.log S ∧
      Real.exp (D * S) * (1 / 2 : ℝ) ^ (2 ^ N) ≤ 1 := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hS0 : 0 < S := (Real.exp_pos 1).trans_le hS
  have hlogS : 1 ≤ Real.log S := by
    have := Real.log_le_log (Real.exp_pos 1) hS
    simpa using this
  let N : ℕ := ⌈2 * Real.log S / Real.log 2⌉₊
  have harg : 0 ≤ 2 * Real.log S / Real.log 2 := by positivity
  have hNlower : 2 * Real.log S ≤ (N : ℝ) * Real.log 2 := by
    exact (div_le_iff₀ htwo).mp (Nat.le_ceil _)
  have hNupper : (N : ℝ) < 2 * Real.log S / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one harg
  have hpow : S ^ 2 ≤ (2 : ℝ) ^ N := by
    calc
      S ^ 2 = Real.exp (2 * Real.log S) := by
        rw [show (2 : ℝ) = (2 : ℕ) from rfl, Real.exp_nat_mul, Real.exp_log hS0]
      _ ≤ Real.exp ((N : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hNlower
      _ = (2 : ℝ) ^ N := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  refine ⟨N, ?_, ?_⟩
  · push_cast
    have heq : 2 * Real.log S / Real.log 2 = (2 / Real.log 2) * Real.log S := by ring
    rw [heq] at hNupper
    nlinarith
  · have hcap : D * S ≤ (2 : ℝ) ^ N * Real.log 2 := by
      calc
        D * S ≤ (S * Real.log 2) * S := mul_le_mul_of_nonneg_right hDS hS0.le
        _ = S ^ 2 * Real.log 2 := by ring
        _ ≤ (2 : ℝ) ^ N * Real.log 2 := mul_le_mul_of_nonneg_right hpow htwo.le
    have hpositive : 0 < Real.exp (D * S) * (1 / 2 : ℝ) ^ (2 ^ N) := by positivity
    apply (Real.log_le_log_iff hpositive zero_lt_one).mp
    rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp, Real.log_pow,
      Real.log_one]
    have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
      ring
    rw [hhalf]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith

/-- The budget above is uniformly `O(log(log b))` for polynomial target
unreduced denominators, without choosing any numerical cutoff. -/
theorem eventually_logarithmic_greedy_budget (D : ℝ) :
    ∃ b0 : ℕ, ∀ b : ℕ, b0 ≤ b →
      ∃ N : ℕ,
        ((N + 1 : ℕ) : ℝ) ≤
          (2 / Real.log 2 + 2) * Real.log (Real.log (b : ℝ)) ∧
        Real.exp (D * Real.log (b : ℝ)) * (1 / 2 : ℝ) ^ (2 ^ N) ≤ 1 := by
  have ht : Filter.Tendsto (fun b : ℕ => Real.log (b : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : ∀ᶠ b : ℕ in Filter.atTop,
      Real.exp 1 ≤ Real.log (b : ℝ) ∧ D / Real.log 2 ≤ Real.log (b : ℝ) :=
    (ht.eventually_ge_atTop (Real.exp 1)).and (ht.eventually_ge_atTop (D / Real.log 2))
  obtain ⟨b0, hb0⟩ := Filter.eventually_atTop.mp he
  refine ⟨b0, fun b hb => ?_⟩
  exact exists_logarithmic_greedy_budget D (Real.log (b : ℝ)) (hb0 b hb).1
    ((div_le_iff₀ htwo).mp (hb0 b hb).2)

end Problem337

end

end OAI
