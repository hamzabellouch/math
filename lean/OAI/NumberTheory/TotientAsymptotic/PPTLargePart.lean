import OAI.NumberTheory.TotientAsymptotic.ComparisonLargePart

namespace OAI

/-!
The leading shift in the PPT construction satisfies the large-prime-part
condition of Ford's comparison lemma directly from normality.  The sharp
bound `Ω(p-1) ≤ 3 B(z)` leaves a strict margin at the published cutoff
`Y₁ ≤ z^(1/(10 B(z)))`.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

private lemma ppt_prime_shift_log_strict : ∀ᶠ z : ℝ in atTop,
    ∀ p : ℕ, p.Prime → z^(9/10 : ℝ) ≤ p →
      (4/5 : ℝ)*Real.log z < Real.log (p-1 : ℕ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (10*Real.log 2))]
    with z hz hlog
  intro p hp hlo
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp' : (p : ℝ)-1 = (p-1 : ℕ) := by
    rw [Nat.cast_sub hp.one_lt.le]
    norm_num
  have hhalf : z^(9/10 : ℝ)/2 ≤ (p-1 : ℕ) := by
    rw [← hp']
    linarith
  have hh := Real.log_le_log
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hz) _) (by norm_num)) hhalf
  rw [Real.log_div (Real.rpow_pos_of_pos (zero_lt_one.trans hz) _).ne'
      (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_rpow (zero_lt_one.trans hz)] at hh
  linarith

lemma ppt_cutoff_log_cost {z Y : ℝ} (hz : 1 < z) (hB : 0 < B z)
    (hY : 1 ≤ Y) (hYu : Y ≤ z^(1/(10*B z))) :
    (3*B z)*Real.log Y ≤ (3/10 : ℝ)*Real.log z := by
  have hl := Real.log_le_log (zero_lt_one.trans_le hY) hYu
  rw [Real.log_rpow (zero_lt_one.trans hz)] at hl
  have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 3*B z)
  have he : (3*B z)*(1/(10*B z)) = (3/10 : ℝ) := by
    field_simp
  rwa [← mul_assoc, he] at hh

/-- The literal cutoff from Ford's comparison parameters suffices for the
large-prime-part requirement on a leading candidate prime. -/
theorem ppt_comparison_large_part : ∀ᶠ z : ℝ in atTop,
    ∀ p : ℕ, ∀ Y : ℝ, p.Prime → z^(9/10 : ℝ) ≤ p →
      1 ≤ Y → Y ≤ z^(1/(10*B z)) →
      ((p-1).primeFactorsList.length : ℝ) ≤ 3*B z →
      Real.sqrt z < (partAbove (p-1) Y : ℝ) := by
  filter_upwards [ppt_prime_shift_log_strict, eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with z hshift hz hB
  intro p Y hp hlo hY hYu hΩ
  apply partAbove_gt_sqrt (Nat.sub_pos_of_lt hp.one_lt) hY hΩ (zero_lt_one.trans hz)
  have hcost := ppt_cutoff_log_cost hz hB hY hYu
  have hlog := hshift p hp hlo
  linarith

/-- Normality supplies the sharp total-factor bound uniformly below `z`.
No separate smooth-divisor exclusion is needed for this conclusion. -/
theorem ppt_normal_comparison_large_part : ∀ᶠ z : ℝ in atTop,
    ∀ (p : ℕ) (S Y : ℝ), 1 < S → 0 ≤ B S → S ≤ z →
      IsNormalPrime S p → z^(9/10 : ℝ) ≤ p → (p-1 : ℕ) ≤ z →
      1 ≤ Y → Y ≤ z^(1/(10*B z)) →
      Real.sqrt z < (partAbove (p-1) Y : ℝ) := by
  filter_upwards [ppt_comparison_large_part,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with z hlarge hBz
  intro p S Y hS hBS hSz hp hlo hpz hY hYu
  have hBSz : B S ≤ B z := Real.log_le_log (Real.log_pos hS)
    (Real.log_le_log (zero_lt_one.trans hS) hSz)
  have hpred : B (p-1 : ℕ) ≤ B z := by
    by_cases hp3 : 3 ≤ p
    · have hp1 : (1 : ℝ) < (p-1 : ℕ) := by
        exact_mod_cast (show 1 < p-1 by omega)
      exact Real.log_le_log (Real.log_pos hp1)
        (Real.log_le_log (zero_lt_one.trans hp1) hpz)
    · have hp2 : p = 2 := by have := hp.1.two_le; omega
      simpa only [hp2, Nat.reduceSub, Nat.cast_one, B, Real.log_one,
        Real.log_zero] using hBz.le
  exact hlarge p Y hp.1 hlo hY hYu
    (normality_total_uniform hp hS hBS hBSz hpred)

end TotientAsymptotic

end

end OAI
