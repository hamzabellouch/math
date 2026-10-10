import OAI.Probability.MatroidProphet.WeightedAccounting
import OAI.Probability.MatroidProphet.Residual.Probability
import Mathlib.Tactic.Positivity

namespace OAI

namespace MatroidProphet

open Finset

lemma weighted_group_payoff (B t κ γ a b ε : ℝ)
    (hB : 1 < B) (ht : 0 ≤ t) (hκ : 0 < κ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (herr : a + b / (B - 1) ≤ ε)
    (levels analyzed : Finset ℤ) (hsub : analyzed ⊆ levels)
    (N Y Λ : ℤ → ℝ) (hN : ∀ i ∈ levels, 0 ≤ N i)
    (hgroup : ∀ i ∈ analyzed,
      t / κ * (γ * Y i - a * N i - b * ∑ l ∈ levels with i < l, N l) ≤ Λ i) :
    t / (2 * κ) * (γ * ∑ i ∈ analyzed, B ^ i * Y i - ε * ∑ i ∈ levels, B ^ i * N i) ≤
      (1 / 2 : ℝ) * ∑ i ∈ analyzed, B ^ i * Λ i := by
  have hB0 : 0 < B := zero_lt_one.trans hB
  have htotal : 0 ≤ ∑ i ∈ levels, B ^ i * N i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (zpow_pos hB0 i).le (hN i hi)
  have hNsum : (∑ i ∈ analyzed, B ^ i * N i) ≤ ∑ i ∈ levels, B ^ i * N i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ =>
      mul_nonneg (zpow_pos hB0 i).le (hN i hi))
  have hcost := higher_weight_cost B hB levels analyzed N hN
  have herrors : a * (∑ i ∈ analyzed, B ^ i * N i) +
      b * (∑ i ∈ analyzed, B ^ i * ∑ l ∈ levels with i < l, N l) ≤
      ε * ∑ i ∈ levels, B ^ i * N i := by
    calc
      _ ≤ a * (∑ i ∈ levels, B ^ i * N i) +
          b * ((∑ i ∈ levels, B ^ i * N i) / (B - 1)) :=
        add_le_add (mul_le_mul_of_nonneg_left hNsum ha) (mul_le_mul_of_nonneg_left hcost hb)
      _ = (a + b / (B - 1)) * ∑ i ∈ levels, B ^ i * N i := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right herr htotal
  have hsum : (∑ i ∈ analyzed,
      B ^ i * (t / κ * (γ * Y i - a * N i - b * ∑ l ∈ levels with i < l, N l))) ≤
      ∑ i ∈ analyzed, B ^ i * Λ i :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hgroup i hi) (zpow_pos hB0 i).le
  have heq : (∑ i ∈ analyzed,
      B ^ i * (t / κ * (γ * Y i - a * N i - b * ∑ l ∈ levels with i < l, N l))) =
      t / κ * (γ * (∑ i ∈ analyzed, B ^ i * Y i) -
        (a * (∑ i ∈ analyzed, B ^ i * N i) +
          b * (∑ i ∈ analyzed, B ^ i * ∑ l ∈ levels with i < l, N l))) := by
    have hi (i : ℤ) : B ^ i * (t / κ * (γ * Y i - a * N i -
        b * ∑ l ∈ levels with i < l, N l)) =
        (t / κ * γ) * (B ^ i * Y i) - (t / κ * a) * (B ^ i * N i) -
          (t / κ * b) * (B ^ i * ∑ l ∈ levels with i < l, N l) := by ring
    simp_rw [hi]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [heq] at hsum
  have hbudget := mul_le_mul_of_nonneg_left
    (sub_le_sub_left herrors (γ * ∑ i ∈ analyzed, B ^ i * Y i)) (div_nonneg ht hκ.le)
  have hresult := hbudget.trans hsum
  calc
    _ = (1 / 2 : ℝ) * (t / κ *
        (γ * ∑ i ∈ analyzed, B ^ i * Y i - ε * ∑ i ∈ levels, B ^ i * N i)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hresult (by norm_num)

lemma source_weighted_group_payoff (levels analyzed : Finset ℤ) (hsub : analyzed ⊆ levels)
    (N Y Λ : ℤ → ℝ) (hN : ∀ i ∈ levels, 0 ≤ N i)
    (hgroup : ∀ i ∈ analyzed,
      thinningRate / densityThreshold *
        (retainedFraction * Y i - (((2 : ℝ) ^ 23)⁻¹ + thinningRate * densityThreshold) * N i -
          (1 + thinningRate * densityThreshold) * ∑ l ∈ levels with i < l, N l) ≤ Λ i) :
    thinningRate / (2 * densityThreshold) *
      (retainedFraction * ∑ i ∈ analyzed, weightBase ^ i * Y i -
        ((2 : ℝ) ^ 21)⁻¹ * ∑ i ∈ levels, weightBase ^ i * N i) ≤
      (1 / 2 : ℝ) * ∑ i ∈ analyzed, weightBase ^ i * Λ i := by
  apply weighted_group_payoff weightBase thinningRate densityThreshold retainedFraction
    (((2 : ℝ) ^ 23)⁻¹ + thinningRate * densityThreshold) (1 + thinningRate * densityThreshold)
    (((2 : ℝ) ^ 21)⁻¹) (by norm_num [weightBase])
    constants_positive.2.2.1.le constants_positive.2.1
  · norm_num [thinningRate, densityThreshold]
  · norm_num [thinningRate, densityThreshold]
  · exact error_constant.le
  · exact hsub
  · exact hN
  · exact hgroup

lemma sum_zpow_le_two_of_bound (B : ℝ) (hB : 2 ≤ B) (levels : Finset ℤ)
    (m : ℝ) (hm : 0 ≤ m) (hbound : ∀ i ∈ levels, B ^ i ≤ m) :
    (∑ i ∈ levels, B ^ i) ≤ 2 * m := by
  classical
  by_cases hn : levels.Nonempty
  · have h := sum_zpow_le_two B hB levels (levels.max' hn)
      (fun i hi => levels.le_max' i hi)
    exact h.trans (mul_le_mul_of_nonneg_left (hbound _ (levels.max'_mem hn)) (by norm_num))
  · have he : levels = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty]
    positivity

lemma small_group_mass_bound (B κ m : ℝ) (hB : 2 ≤ B) (hκ : 0 ≤ κ) (hm : 0 ≤ m)
    (levels : Finset ℤ) (Y : ℤ → ℝ) (hY : ∀ i ∈ levels, Y i ≤ κ)
    (hbound : ∀ i ∈ levels, B ^ i ≤ m) :
    (∑ i ∈ levels, B ^ i * Y i) ≤ 2 * κ * m := by
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  calc
    _ ≤ ∑ i ∈ levels, B ^ i * κ :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hY i hi) (zpow_pos hB0 i).le
    _ = κ * ∑ i ∈ levels, B ^ i := by rw [← Finset.sum_mul]; ring
    _ ≤ κ * (2 * m) := mul_le_mul_of_nonneg_left
      (sum_zpow_le_two_of_bound B hB levels m hm hbound) hκ
    _ = _ := by ring

lemma bitsExpectation_sub {α : Type*} [DecidableEq α] (q : α → ℝ) (V : Finset α)
    (f g : Finset α → ℝ) :
    bitsExpectation q V (fun H => f H - g H) = bitsExpectation q V f - bitsExpectation q V g := by
  simp only [bitsExpectation, mul_sub, Finset.sum_sub_distrib]

lemma main_branch_from_filter {α : Type*} [DecidableEq α] (V : Finset α)
    (bigY allY massU payoff : Finset α → ℝ) (W m : ℝ)
    (hW : 0 ≤ W) (hm : m ≤ W / (8 * densityThreshold))
    (hY : bitsExpectation (fun _ => (1 / 2 : ℝ)) V allY = W / 2)
    (hU : bitsExpectation (fun _ => (1 / 2 : ℝ)) V massU ≤ W)
    (hsmall : ∀ H ⊆ V, allY H ≤ bigY H + 2 * densityThreshold * m)
    (hpay : ∀ H ⊆ V, thinningRate / (2 * densityThreshold) *
      (retainedFraction * bigY H - ((2 : ℝ) ^ 21)⁻¹ * massU H) ≤ payoff H) :
    thinningRate * retainedFraction / (16 * densityThreshold) * W ≤
      bitsExpectation (fun _ => (1 / 2 : ℝ)) V payoff := by
  let q : α → ℝ := fun _ => 1 / 2
  have hq0 : ∀ e, 0 ≤ q e := fun _ => by norm_num [q]
  have hq1 : ∀ e, q e ≤ 1 := fun _ => by norm_num [q]
  have hybig := bitsExpectation_mono q hq0 hq1 V hsmall
  rw [bitsExpectation_add, bitsExpectation_const, hY] at hybig
  have hbig : W / 4 ≤ bitsExpectation q V bigY := by
    have hk : 0 < densityThreshold := constants_positive.2.1
    have hmul := (le_div_iff₀ (by positivity : 0 < 8 * densityThreshold)).mp hm
    nlinarith
  have hpaid := bitsExpectation_mono q hq0 hq1 V hpay
  rw [bitsExpectation_mul_const, bitsExpectation_sub,
    bitsExpectation_mul_const, bitsExpectation_mul_const] at hpaid
  have hinner : retainedFraction / 8 * W ≤
      retainedFraction * bitsExpectation q V bigY -
        ((2 : ℝ) ^ 21)⁻¹ * bitsExpectation q V massU := by
    have hγ := constants_positive.2.2.2.2
    have h1 := mul_le_mul_of_nonneg_left hbig hγ.le
    have h2 := mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ ((2 : ℝ) ^ 21)⁻¹)
    have h3 := mul_le_mul_of_nonneg_right retained_fraction_slack hW
    nlinarith
  have hscale : 0 ≤ thinningRate / (2 * densityThreshold) :=
    div_nonneg constants_positive.2.2.1.le
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) constants_positive.2.1.le)
  have hscaled := mul_le_mul_of_nonneg_left hinner hscale
  have hfinal := hscaled.trans hpaid
  have he : thinningRate / (2 * densityThreshold) * (retainedFraction / 8 * W) =
      thinningRate * retainedFraction / (16 * densityThreshold) * W := by ring
  rw [he] at hfinal
  exact hfinal

end MatroidProphet

end OAI
