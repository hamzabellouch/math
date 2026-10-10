import Mathlib

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem310.WindowBudget

/-- A polynomial factor times a decaying exponential tends to zero along natural arguments. -/
lemma tendsto_nat_mul_exp_neg (a : ℝ) (ha : 0 < a) :
    Tendsto (fun r : ℕ => (r : ℝ) * Real.exp (-a * (r : ℝ))) atTop (𝓝 0) := by
  simpa [Function.comp_def] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) a ha).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The entropy factor appearing in the finite scale discretization is dominated by
its exponential saving. This uses exactly the numerical coefficient. -/
lemma entropy_tendsto_zero (M a : ℝ) (ha : 10 ≤ a) :
    Tendsto (fun r : ℕ => 20 * M * (r : ℝ) * (1 + (2 : ℝ) ^ (2 * r + 2)) *
      Real.exp (-a * (r : ℝ))) atTop (𝓝 0) := by
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < a - 2 * Real.log 2 := by linarith
  have h1 := (tendsto_nat_mul_exp_neg a ha0).const_mul (20 * M)
  have h2 := (tendsto_nat_mul_exp_neg (a - 2 * Real.log 2) hb0).const_mul (80 * M)
  have hsum := h1.add h2
  simp only [mul_zero, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [] with r
  have hpow : (2 : ℝ) ^ (2 * r + 2) =
      Real.exp (((2 * r + 2 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hfour : Real.exp (2 * Real.log 2) = 4 := by
    convert Real.exp_nat_mul (Real.log 2) 2 using 1
    norm_num [Real.exp_log]
  have hprod : (2 : ℝ) ^ (2 * r + 2) * Real.exp (-a * (r : ℝ)) =
      4 * Real.exp (-(a - 2 * Real.log 2) * (r : ℝ)) := by
    rw [hpow, ← Real.exp_add, ← hfour, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc
    20 * M * ((r : ℝ) * Real.exp (-a * (r : ℝ))) +
        80 * M * ((r : ℝ) * Real.exp (-(a - 2 * Real.log 2) * (r : ℝ))) =
        20 * M * (r : ℝ) * Real.exp (-a * (r : ℝ)) +
        20 * M * (r : ℝ) * ((2 : ℝ) ^ (2 * r + 2) * Real.exp (-a * (r : ℝ))) := by
          rw [hprod]
          ring
    _ = _ := by ring

/-- A single lower bound on the window length works for every larger window. -/
lemma exists_entropy_threshold (p M a : ℝ) (hp : 0 < p) (ha : 10 ≤ a) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      20 * M * (r : ℝ) * (1 + (2 : ℝ) ^ (2 * r + 2)) *
        Real.exp (-a * (r : ℝ)) < p := by
  have h := (entropy_tendsto_zero M a ha).eventually_lt_const hp
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.mp h
  refine ⟨max 1 r₀, le_max_left _ _, ?_⟩
  intro r hr
  exact hr₀ r ((le_max_right _ _).trans hr)

/-- Choose the branching number with the required exponential margin. -/
lemma exists_branching_number (p : ℝ) (hp : 0 < p) :
    ∃ M : ℕ, 2 ≤ M ∧ 10 ≤ p * ((M : ℝ) - 1) / 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (20 / p)
  have hprod : 20 < (N : ℝ) * p := (div_lt_iff₀ hp).mp hN
  refine ⟨N + 2, by omega, ?_⟩
  push_cast
  nlinarith

/-- A geometric probability can be made arbitrarily small at a positive depth. -/
lemma exists_positive_depth (p q : ℝ) (hp : 0 < p) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ d : ℕ, 1 ≤ d ∧ q ^ d < p := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).eventually_lt_const hp
  obtain ⟨d, hd⟩ := eventually_atTop.mp h
  exact ⟨max 1 d, le_max_left _ _, hd _ (le_max_right _ _)⟩

/-- The branching factor and tree depth can be chosen in the prescribed order. -/
lemma exists_tree_parameters (p : ℝ) (hp : 0 < p) :
    ∃ M d : ℕ, 2 ≤ M ∧ 1 ≤ d ∧
      10 ≤ p * ((M : ℝ) - 1) / 2 ∧
      (1 - ((2 : ℝ)⁻¹) ^ (M - 1)) ^ d < p := by
  obtain ⟨M, hM, hmargin⟩ := exists_branching_number p hp
  have hpowpos : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ (M - 1) := by positivity
  have hpowle : ((2 : ℝ)⁻¹) ^ (M - 1) ≤ (1 : ℝ) := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨d, hd, hsmall⟩ := exists_positive_depth p
    (1 - ((2 : ℝ)⁻¹) ^ (M - 1)) hp (by linarith) (by linarith)
  exact ⟨M, d, hM, hd, hmargin, hsmall⟩

/-- Choose a gap after the finite tree has been fixed. The expression is `K 2^(2-g)`
written without subtraction in a natural-number exponent. -/
lemma exists_gap (p : ℝ) (hp : 0 < p) (K : ℕ) :
    ∃ g : ℕ, 1 ≤ g ∧ (K : ℝ) * 4 * ((2 : ℝ)⁻¹) ^ g < p := by
  have hlim : Tendsto (fun g : ℕ => (K : ℝ) * 4 * ((2 : ℝ)⁻¹) ^ g)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul ((K : ℝ) * 4)
  obtain ⟨g, hg⟩ := eventually_atTop.mp (hlim.eventually_lt_const hp)
  exact ⟨max 1 g, le_max_left _ _, hg _ (le_max_right _ _)⟩

/-- The elementary Bernoulli miss probability is bounded by an exponential. -/
lemma one_sub_pow_le_exp (u : ℝ) (hu : u ≤ 1) (N : ℕ) :
    (1 - u) ^ N ≤ Real.exp (-u * (N : ℝ)) := by
  have hbase : 1 - u ≤ Real.exp (-u) := by
    have h := Real.add_one_le_exp (-u)
    linarith
  calc
    (1 - u) ^ N ≤ Real.exp (-u) ^ N :=
      pow_le_pow_left₀ (by linarith) hbase N
    _ = Real.exp (-u * (N : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The window threshold also bounds the actual fixed-scale failure probability
multiplied by the number of scale representatives. -/
lemma exists_probability_threshold (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (M : ℕ) (hM : 2 ≤ M) (hmargin : 10 ≤ p * ((M : ℝ) - 1) / 2) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      20 * (M : ℝ) * (r : ℝ) * (1 + (2 : ℝ) ^ (2 * r + 2)) *
        (1 - p / 2) ^ ((M - 1) * r) < p := by
  obtain ⟨r₀, hr₀, hsmall⟩ :=
    exists_entropy_threshold p M (p * ((M : ℝ) - 1) / 2) hp hmargin
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr
  have hpow := one_sub_pow_le_exp (p / 2) (by linarith) ((M - 1) * r)
  have hexp : -(p / 2) * (((M - 1) * r : ℕ) : ℝ) =
      -(p * ((M : ℝ) - 1) / 2) * (r : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ M)]
    push_cast
    ring
  rw [hexp] at hpow
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hpow (by positivity)) (hsmall r hr)

end Problem310.WindowBudget

end

end OAI
