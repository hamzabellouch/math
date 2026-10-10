import OAI.Combinatorics.Ryser.Selection.AnalyticalLimits
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum

namespace OAI

open Filter Topology

namespace RyserCoveringCounterexample.Selection

theorem chunk_tail_le_exp_of_log_bounds (α γ B q : ℝ)
    (hα : 0 ≤ α) (hB : 0 < B) (hq : 1 ≤ q)
    (hbase : Real.log B ≤ Real.log q / 2)
    (hbudget : (α + 1) * Real.log 2 + γ * Real.log B ≤ (γ / 4) * Real.log q) :
    (2 : ℝ) ^ Nat.ceil (α * q) * (B / Real.sqrt q) ^ Nat.ceil (γ * q) ≤
      Real.exp (-(γ / 4) * q * Real.log q) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hspos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqpos
  have hratio : 0 < B / Real.sqrt q := div_pos hB hspos
  have hlogratio : Real.log (B / Real.sqrt q) = Real.log B - Real.log q / 2 := by
    rw [Real.log_div hB.ne' hspos.ne', Real.log_sqrt hqpos.le]
  have hlognonpos : Real.log (B / Real.sqrt q) ≤ 0 := by
    rw [hlogratio]
    linarith
  have hceilα : (Nat.ceil (α * q) : ℝ) ≤ (α + 1) * q := by
    calc
      (Nat.ceil (α * q) : ℝ) ≤ α * q + 1 :=
        (Nat.ceil_lt_add_one (mul_nonneg hα hqpos.le)).le
      _ ≤ (α + 1) * q := by nlinarith
  have hfirst : (Nat.ceil (α * q) : ℝ) * Real.log 2 ≤
      (α + 1) * q * Real.log 2 :=
    mul_le_mul_of_nonneg_right hceilα (Real.log_nonneg (by norm_num))
  have hsecond : (Nat.ceil (γ * q) : ℝ) * Real.log (B / Real.sqrt q) ≤
      γ * q * Real.log (B / Real.sqrt q) :=
    mul_le_mul_of_nonpos_right (Nat.le_ceil (γ * q)) hlognonpos
  have htwo : (2 : ℝ) ^ Nat.ceil (α * q) =
      Real.exp ((Nat.ceil (α * q) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hpower : (B / Real.sqrt q) ^ Nat.ceil (γ * q) =
      Real.exp ((Nat.ceil (γ * q) : ℝ) * Real.log (B / Real.sqrt q)) := by
    rw [Real.exp_nat_mul, Real.exp_log hratio]
  rw [htwo, hpower, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    (Nat.ceil (α * q) : ℝ) * Real.log 2 +
        (Nat.ceil (γ * q) : ℝ) * Real.log (B / Real.sqrt q) ≤
        (α + 1) * q * Real.log 2 + γ * q * Real.log (B / Real.sqrt q) :=
      add_le_add hfirst hsecond
    _ = q * ((α + 1) * Real.log 2 + γ * Real.log B - (γ / 2) * Real.log q) := by
      rw [hlogratio]
      ring
    _ ≤ q * ((γ / 4) * Real.log q - (γ / 2) * Real.log q) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hbudget _) hqpos.le
    _ = -(γ / 4) * q * Real.log q := by ring

theorem exists_threshold_chunk_tail (α γ B : ℝ)
    (hα : 0 ≤ α) (hγ : 0 < γ) (hB : 0 < B) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      (2 : ℝ) ^ Nat.ceil (α * (q : ℝ)) *
          (B / Real.sqrt (q : ℝ)) ^ Nat.ceil (γ * (q : ℝ)) ≤
        Real.exp (-(γ / 4) * (q : ℝ) * Real.log (q : ℝ)) := by
  have hlog : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hhalf : Tendsto (fun q : ℕ => (1 / 2 : ℝ) * Real.log (q : ℝ)) atTop atTop :=
    hlog.const_mul_atTop (by norm_num)
  have hquarter : Tendsto (fun q : ℕ => (γ / 4) * Real.log (q : ℝ)) atTop atTop :=
    hlog.const_mul_atTop (div_pos hγ (by norm_num))
  have hev : ∀ᶠ q : ℕ in atTop,
      (2 : ℝ) ^ Nat.ceil (α * (q : ℝ)) *
          (B / Real.sqrt (q : ℝ)) ^ Nat.ceil (γ * (q : ℝ)) ≤
        Real.exp (-(γ / 4) * (q : ℝ) * Real.log (q : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hhalf.eventually_ge_atTop (Real.log B),
      hquarter.eventually_ge_atTop ((α + 1) * Real.log 2 + γ * Real.log B)]
      with q hq hbase hbudget
    have hqreal : (1 : ℝ) ≤ (q : ℝ) := by
      simpa only [Nat.cast_one] using (Nat.cast_le (α := ℝ)).mpr hq
    exact chunk_tail_le_exp_of_log_bounds α γ B (q : ℝ) hα hB hqreal
      (by linarith) hbudget
  exact eventually_atTop.1 hev

theorem exists_threshold_pool_budget (K D γ : ℝ) (hγ : 0 < γ) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      K * D * Real.sqrt (q : ℝ) ≤ γ * (q : ℝ) := by
  have hs : Tendsto (fun q : ℕ => Real.sqrt (q : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hr : Tendsto (fun q : ℕ => K * D / Real.sqrt (q : ℝ)) atTop (𝓝 0) :=
    hs.const_div_atTop (K * D)
  have hev : ∀ᶠ q : ℕ in atTop,
      K * D * Real.sqrt (q : ℝ) ≤ γ * (q : ℝ) := by
    filter_upwards [hr.eventually (gt_mem_nhds hγ), hs.eventually_ge_atTop 1]
      with q hq hs1
    have hspos : 0 < Real.sqrt (q : ℝ) := lt_of_lt_of_le zero_lt_one hs1
    have hKD : K * D ≤ γ * Real.sqrt (q : ℝ) :=
      (div_le_iff₀ hspos).mp hq.le
    calc
      K * D * Real.sqrt (q : ℝ) ≤
          (γ * Real.sqrt (q : ℝ)) * Real.sqrt (q : ℝ) :=
        mul_le_mul_of_nonneg_right hKD (Real.sqrt_nonneg _)
      _ = γ * (q : ℝ) := by
        rw [mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg q)]
  exact eventually_atTop.1 hev

theorem exists_threshold_chunk_tail_and_pool_budget (α γ B K D : ℝ)
    (hα : 0 ≤ α) (hγ : 0 < γ) (hB : 0 < B) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      ((2 : ℝ) ^ Nat.ceil (α * (q : ℝ)) *
          (B / Real.sqrt (q : ℝ)) ^ Nat.ceil (γ * (q : ℝ)) ≤
        Real.exp (-(γ / 4) * (q : ℝ) * Real.log (q : ℝ))) ∧
      K * D * Real.sqrt (q : ℝ) ≤ γ * (q : ℝ) := by
  obtain ⟨Q₁, hQ₁⟩ := exists_threshold_chunk_tail α γ B hα hγ hB
  obtain ⟨Q₂, hQ₂⟩ := exists_threshold_pool_budget K D γ hγ
  refine ⟨max Q₁ Q₂, ?_⟩
  intro q hq
  exact ⟨hQ₁ q ((le_max_left _ _).trans hq), hQ₂ q ((le_max_right _ _).trans hq)⟩

theorem chunk_tail_le_exp_of_length_le (α γ B q : ℝ) (N : ℕ)
    (hB : 0 ≤ B) (hN : (N : ℝ) ≤ α * q)
    (hceil : (2 : ℝ) ^ Nat.ceil (α * q) *
      (B / Real.sqrt q) ^ Nat.ceil (γ * q) ≤ Real.exp (-(γ / 4) * q * Real.log q)) :
    (2 : ℝ) ^ N * (B / Real.sqrt q) ^ Nat.ceil (γ * q) ≤
      Real.exp (-(γ / 4) * q * Real.log q) := by
  have hN' : N ≤ Nat.ceil (α * q) :=
    (Nat.cast_le (α := ℝ)).mp (hN.trans (Nat.le_ceil (α * q)))
  have hpow : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ Nat.ceil (α * q) :=
    pow_le_pow_right₀ (by norm_num) hN'
  exact (mul_le_mul_of_nonneg_right hpow
    (pow_nonneg (div_nonneg hB (Real.sqrt_nonneg q)) _)).trans hceil

end RyserCoveringCounterexample.Selection

end OAI
