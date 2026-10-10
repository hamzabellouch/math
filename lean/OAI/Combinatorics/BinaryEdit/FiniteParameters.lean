import Mathlib

namespace OAI

namespace TreeEdit.BinaryLower.Parameters

/-- Binary word length for the quadratic-width code, with source length `(20 * k * k^(20*k))^k`. -/
def finiteLength (k : ℕ) : ℕ := (20 * k * k ^ (20 * k)) ^ (3 * k)

lemma finiteLength_pos {k : ℕ} (hk : 0 < k) : 0 < finiteLength k := by
  unfold finiteLength
  positivity

lemma log_finiteLength {k : ℕ} (hk : 0 < k) :
    Real.log (finiteLength k : ℝ) =
      60 * (k : ℝ) ^ 2 * Real.log k + 3 * k * Real.log (20 * k) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  unfold finiteLength
  push_cast
  rw [Real.log_pow, Real.log_mul (by positivity : (20 : ℝ) * k ≠ 0)
    (pow_ne_zero _ hkR), Real.log_pow]
  push_cast
  ring

lemma finiteLength_log_succ_le {k : ℕ} (hk : 20 ≤ k) :
    Real.log (finiteLength (k + 1) : ℝ) ≤
      300 * (k : ℝ) ^ 2 * Real.log k := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have hx : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hxk : (k : ℝ) + 1 ≤ (k : ℝ) ^ 2 := by nlinarith
  have hlogx : Real.log ((k : ℝ) + 1) ≤ 2 * Real.log k := by
    calc
      Real.log ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) ^ 2) :=
        Real.log_le_log hx hxk
      _ = 2 * Real.log k := by rw [Real.log_pow]; norm_num
  have hk2 : (400 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hprod : 20 * ((k : ℝ) + 1) ≤ (k : ℝ) ^ 3 := by
    have := mul_le_mul_of_nonneg_right hk2 (le_of_lt hkpos)
    nlinarith
  have hlogprod : Real.log (20 * ((k : ℝ) + 1)) ≤ 3 * Real.log k := by
    calc
      Real.log (20 * ((k : ℝ) + 1)) ≤ Real.log ((k : ℝ) ^ 3) :=
        Real.log_le_log (by positivity) hprod
      _ = 3 * Real.log k := by rw [Real.log_pow]; norm_num
  have hsq : ((k : ℝ) + 1) ^ 2 ≤ (3 / 2 : ℝ) * (k : ℝ) ^ 2 := by
    nlinarith
  have hterm1 : 60 * ((k : ℝ) + 1) ^ 2 * Real.log ((k : ℝ) + 1) ≤
      180 * (k : ℝ) ^ 2 * Real.log k := by
    calc
      _ ≤ 60 * ((k : ℝ) + 1) ^ 2 * (2 * Real.log k) :=
        mul_le_mul_of_nonneg_left hlogx (by positivity)
      _ ≤ 60 * ((3 / 2 : ℝ) * (k : ℝ) ^ 2) * (2 * Real.log k) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by positivity)
      _ = _ := by ring
  have hterm2 : 3 * ((k : ℝ) + 1) * Real.log (20 * ((k : ℝ) + 1)) ≤
      18 * (k : ℝ) ^ 2 * Real.log k := by
    calc
      _ ≤ 3 * ((k : ℝ) + 1) * (3 * Real.log k) :=
        mul_le_mul_of_nonneg_left hlogprod (by positivity)
      _ ≤ 18 * (k : ℝ) ^ 2 * Real.log k := by
        have := mul_le_mul_of_nonneg_right hxk hlog
        nlinarith
  rw [log_finiteLength (by omega : 0 < k + 1)]
  push_cast
  nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) hlog]

lemma le_finiteLength {k : ℕ} (hk : 0 < k) : k ≤ finiteLength k := by
  have hp : 1 ≤ k ^ (20 * k) := Nat.one_le_pow _ _ hk
  have hb : k ≤ 20 * k * k ^ (20 * k) := by
    have := Nat.mul_le_mul_left (20 * k) hp
    nlinarith
  exact hb.trans (Nat.le_pow (by omega : 0 < 3 * k))

lemma finiteLength_log_succ_pos {k : ℕ} (hk : 20 ≤ k) :
    0 < Real.log (finiteLength (k + 1) : ℝ) := by
  apply Real.log_pos
  have := le_finiteLength (by omega : 0 < k + 1)
  exact_mod_cast (show 1 < finiteLength (k + 1) by omega)

lemma finiteLength_loglog_succ_le {k : ℕ} (hk : 20 ≤ k) :
    Real.log (Real.log (finiteLength (k + 1) : ℝ)) ≤
      5 * Real.log k := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hk2 : (300 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hlog : Real.log (k : ℝ) ≤ k := Real.log_le_self hk0
  have hbound : Real.log (finiteLength (k + 1) : ℝ) ≤ (k : ℝ) ^ 5 := by
    calc
      _ ≤ 300 * (k : ℝ) ^ 2 * Real.log k := finiteLength_log_succ_le hk
      _ ≤ 300 * (k : ℝ) ^ 3 := by
        have := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 300 * (k : ℝ) ^ 2 by positivity)
        nlinarith
      _ ≤ (k : ℝ) ^ 5 := by
        have := mul_le_mul_of_nonneg_right hk2 (pow_nonneg hk0 3)
        nlinarith
  calc
    _ ≤ Real.log ((k : ℝ) ^ 5) :=
      Real.log_le_log (finiteLength_log_succ_pos hk) hbound
    _ = 5 * Real.log k := by rw [Real.log_pow]; norm_num

lemma finite_lower_log_bound {c₀ : ℝ} (hc₀ : 0 < c₀) {k : ℕ}
    (hk : 20 ≤ k) (hkc : -4 * Real.log c₀ ≤ (k : ℝ)) :
    (1 / 4 : ℝ) * k * Real.log k ≤
      Real.log (c₀ * ((k : ℝ) / 4) ^ k) := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hlog1 : 1 ≤ Real.log (k : ℝ) := by
    apply (Real.le_log_iff_exp_le hkpos).2
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hlog4 : 2 * Real.log 4 ≤ Real.log (k : ℝ) := by
    calc
      2 * Real.log 4 = Real.log ((4 : ℝ) ^ 2) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.log (k : ℝ) := Real.log_le_log (by positivity) (by norm_num; linarith)
  rw [Real.log_mul hc₀.ne' (by positivity), Real.log_pow,
    Real.log_div hkpos.ne' (by norm_num : (4 : ℝ) ≠ 0)]
  have hmul1 := mul_le_mul_of_nonneg_left hlog1 (le_of_lt hkpos)
  have hmul4 := mul_le_mul_of_nonneg_left hlog4 (le_of_lt hkpos)
  nlinarith

lemma eventually_finite_lower_log_bound {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (1 / 4 : ℝ) * k * Real.log k ≤
        Real.log (c₀ * ((k : ℝ) / 4) ^ k) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (-4 * Real.log c₀)
  refine ⟨max 20 n, ?_⟩
  intro k hk
  apply finite_lower_log_bound hc₀ (le_trans (le_max_left _ _) hk)
  exact hn.trans (by exact_mod_cast (le_trans (le_max_right 20 n) hk))

/-- The logarithmic scale at any cap below the next construction length. -/
lemma finite_cap_sqrt_bound {k d : ℕ} (hk : 20 ≤ k) (hd : 2 ≤ d)
    (hcap : d ≤ finiteLength (k + 1)) :
    Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ))) ≤
      40 * k * Real.log k := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith only [hkR])
  have hdR : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hdlog : 0 < Real.log (d : ℝ) := Real.log_pos hdR
  have hlogcap : Real.log (d : ℝ) ≤ Real.log (finiteLength (k + 1) : ℝ) :=
    Real.log_le_log (lt_trans zero_lt_one hdR) (Nat.cast_le.mpr hcap)
  have hlogbound : Real.log (d : ℝ) ≤ 300 * (k : ℝ) ^ 2 * Real.log k :=
    hlogcap.trans (finiteLength_log_succ_le hk)
  have hloglogbound : Real.log (Real.log (d : ℝ)) ≤ 5 * Real.log k :=
    (Real.log_le_log hdlog hlogcap).trans (finiteLength_loglog_succ_le hk)
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (mul_nonneg (by norm_num) hk0) hlogk, ?_⟩
  have h1 := mul_le_mul_of_nonneg_left hloglogbound hdlog.le
  have h2 := mul_le_mul_of_nonneg_right hlogbound
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hlogk)
  have h3 : 0 ≤ (k : ℝ) ^ 2 * Real.log k ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith only [h1, h2, h3]

/-- Numerical transfer from a finite-family distortion to an intervening cap. -/
lemma finite_cap_exponential_bound {c₀ : ℝ} (hc₀ : 0 < c₀) {k d : ℕ}
    (hk : 20 ≤ k) (hkc : -4 * Real.log c₀ ≤ (k : ℝ))
    (hd : 2 ≤ d) (hcap : d ≤ finiteLength (k + 1)) :
    Real.exp ((1 / 160 : ℝ) *
      Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ)))) ≤
        c₀ * ((k : ℝ) / 4) ^ k := by
  have hsqrt := finite_cap_sqrt_bound hk hd hcap
  have hlower := finite_lower_log_bound hc₀ hk hkc
  have hexponent : (1 / 160 : ℝ) *
      Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ))) ≤
        Real.log (c₀ * ((k : ℝ) / 4) ^ k) := by nlinarith only [hsqrt, hlower]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  calc
    _ ≤ Real.exp (Real.log (c₀ * ((k : ℝ) / 4) ^ k)) :=
      Real.exp_le_exp.mpr hexponent
    _ = _ := Real.exp_log (by positivity)

/-- Choose adjacent construction lengths bracketing a cap.  No strict
monotonicity of the length sequence is needed for this selection argument. -/
lemma exists_finiteLength_bracket {k₀ d : ℕ} (hk₀ : 0 < k₀)
    (hd : finiteLength k₀ ≤ d) :
    ∃ k : ℕ, k₀ ≤ k ∧ finiteLength k ≤ d ∧ d < finiteLength (k + 1) := by
  have hex : ∃ n : ℕ, d < finiteLength (k₀ + n + 1) := by
    refine ⟨d, ?_⟩
    have hb := le_finiteLength (by omega : 0 < k₀ + d + 1)
    omega
  let n : ℕ := Nat.find hex
  refine ⟨k₀ + n, by omega, ?_, ?_⟩
  · by_cases hn : n = 0
    · simpa only [hn, Nat.add_zero] using hd
    · have hmin := Nat.find_min hex (m := n - 1) (by dsimp [n] at hn ⊢; omega)
      have heq : k₀ + (n - 1) + 1 = k₀ + n := by omega
      rw [heq] at hmin
      exact Nat.le_of_not_gt hmin
  · exact Nat.find_spec hex

/-- The complete numerical all-large-cap selection used after constructing the
finite-tree witness family.  The requested lower threshold `K` is arbitrary. -/
lemma exists_finite_cap_parameters {c₀ : ℝ} (hc₀ : 0 < c₀) (K : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ k : ℕ,
      K ≤ k ∧ 20 ≤ k ∧ finiteLength k ≤ d ∧
        Real.exp ((1 / 160 : ℝ) *
          Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ)))) ≤
            c₀ * ((k : ℝ) / 4) ^ k := by
  obtain ⟨n, hn⟩ := exists_nat_ge (-4 * Real.log c₀)
  let k₀ : ℕ := max 20 (max K n)
  have hk20 : 20 ≤ k₀ := le_max_left _ _
  have hkK : K ≤ k₀ := (le_max_left K n).trans (le_max_right 20 (max K n))
  have hkn : n ≤ k₀ := (le_max_right K n).trans (le_max_right 20 (max K n))
  refine ⟨finiteLength k₀, ?_⟩
  intro d hd
  obtain ⟨k, hk₀, hkd, hdk⟩ := exists_finiteLength_bracket (by omega : 0 < k₀) hd
  have hk : 20 ≤ k := hk20.trans hk₀
  have hkc : -4 * Real.log c₀ ≤ (k : ℝ) :=
    hn.trans (Nat.cast_le.mpr (hkn.trans hk₀))
  have hd2 : 2 ≤ d := by
    have := le_finiteLength (by omega : 0 < k)
    omega
  exact ⟨k, hkK.trans hk₀, hk, hkd,
    finite_cap_exponential_bound hc₀ hk hkc hd2 hdk.le⟩

end TreeEdit.BinaryLower.Parameters

end OAI
