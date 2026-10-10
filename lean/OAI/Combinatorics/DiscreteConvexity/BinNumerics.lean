import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace TalagrandDiscreteConvexity

open scoped BigOperators

private theorem half_range_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i) + 2 * (1 / 2 : ℝ) ^ n = 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith [ih]

private theorem finite_half_sum_le_two (s : Finset ℕ) :
    (∑ i ∈ s, (1 / 2 : ℝ) ^ i) ≤ 2 := by
  have hsub : s ⊆ Finset.range (s.sup id + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  have hle : (∑ i ∈ s, (1 / 2 : ℝ) ^ i) ≤
      ∑ i ∈ Finset.range (s.sup id + 1), (1 / 2 : ℝ) ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro i hi hnot
      positivity)
  have hgeom := half_range_sum (s.sup id + 1)
  have hp : 0 ≤ (1 / 2 : ℝ) ^ (s.sup id + 1) := by positivity
  linarith

private theorem finite_small_base_sum_le_two (s : Finset ℕ) {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1 / 2) : (∑ i ∈ s, a ^ i) ≤ 2 := by
  calc
    (∑ i ∈ s, a ^ i) ≤ ∑ i ∈ s, (1 / 2 : ℝ) ^ i :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ ha ha' i)
    _ ≤ 2 := finite_half_sum_le_two s

private theorem finite_quadrant_sum_le_four (T : Finset (ℕ × ℕ)) {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1 / 2) :
    (∑ c ∈ T, a ^ c.1 * a ^ c.2) ≤ 4 := by
  have hsub : T ⊆ (T.image Prod.fst) ×ˢ (T.image Prod.snd) := by
    intro c hc
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hc, Finset.mem_image_of_mem _ hc⟩
  calc
    (∑ c ∈ T, a ^ c.1 * a ^ c.2) ≤
        ∑ c ∈ (T.image Prod.fst) ×ˢ (T.image Prod.snd), a ^ c.1 * a ^ c.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro c hc hnot
        exact mul_nonneg (pow_nonneg ha _) (pow_nonneg ha _))
    _ = (∑ i ∈ T.image Prod.fst, a ^ i) * (∑ j ∈ T.image Prod.snd, a ^ j) := by
      rw [Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ 2 * 2 :=
      mul_le_mul (finite_small_base_sum_le_two _ ha ha')
        (finite_small_base_sum_le_two _ ha ha')
        (Finset.sum_nonneg fun _ _ => pow_nonneg ha _) (by norm_num)
    _ = 4 := by norm_num

/-- A finite occupied-bin estimate, with no infinite-series premise. -/
theorem finite_bin_geometric_bound (B : Finset (ℕ × ℕ))
    (hB : ∀ b ∈ B, 1 ≤ b.1 ∧ 64 * b.1 ≤ b.2) {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1 / 2) :
    (∑ b ∈ B, a ^ b.2) ≤ 4 * a ^ 64 := by
  let shift : ℕ × ℕ → ℕ × ℕ := fun b => (b.1 - 1, b.2 - b.1 - 63)
  have hinj : Set.InjOn shift B := by
    intro b hb c hc heq
    have hb' := hB b hb
    have hc' := hB c hc
    have heq₁ : b.1 - 1 = c.1 - 1 := congrArg Prod.fst heq
    have heq₂ : b.2 - b.1 - 63 = c.2 - c.1 - 63 := congrArg Prod.snd heq
    apply Prod.ext <;> omega
  have heq : (∑ b ∈ B, a ^ b.2) =
      a ^ 64 * ∑ c ∈ B.image shift, a ^ c.1 * a ^ c.2 := by
    rw [Finset.mul_sum, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro b hb
    have hb' := hB b hb
    have hexp : b.2 = 64 + (b.1 - 1) + (b.2 - b.1 - 63) := by omega
    change a ^ b.2 = a ^ 64 * (a ^ (b.1 - 1) * a ^ (b.2 - b.1 - 63))
    calc
      a ^ b.2 = a ^ (64 + (b.1 - 1) + (b.2 - b.1 - 63)) := congrArg (a ^ ·) hexp
      _ = a ^ 64 * (a ^ (b.1 - 1) * a ^ (b.2 - b.1 - 63)) := by
        simp only [pow_add, mul_assoc]
  rw [heq]
  calc
    a ^ 64 * (∑ c ∈ B.image shift, a ^ c.1 * a ^ c.2) ≤ a ^ 64 * 4 :=
      mul_le_mul_of_nonneg_left (finite_quadrant_sum_le_four _ ha ha')
        (pow_nonneg ha _)
    _ = 4 * a ^ 64 := mul_comm _ _

/-- The total bin-cover cost is strictly below one quarter. -/
theorem finite_bin_cost_lt_quarter (B : Finset (ℕ × ℕ))
    (hB : ∀ b ∈ B, 1 ≤ b.1 ∧ 64 * b.1 ≤ b.2) :
    (∑ b ∈ B, 3 * (1 / 2 : ℝ) ^ b.2) < 1 / 4 := by
  rw [← Finset.mul_sum]
  have h := finite_bin_geometric_bound B hB (a := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)
  have hn : (3 : ℝ) * (4 * (1 / 2 : ℝ) ^ 64) < 1 / 4 := by norm_num
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h (by norm_num)) hn

/-- The total contribution of uncovered bins is below the exceptional threshold. -/
theorem finite_bin_power_lt_threshold (B : Finset (ℕ × ℕ))
    (hB : ∀ b ∈ B, 1 ≤ b.1 ∧ 64 * b.1 ≤ b.2) :
    (∑ b ∈ B, (1 / 2 : ℝ) ^ (4 * b.2)) < (1 / 2 : ℝ) ^ 32 := by
  have h := finite_bin_geometric_bound B hB (a := (1 / 2 : ℝ) ^ 4)
    (by norm_num) (by norm_num)
  have heq : (∑ b ∈ B, (1 / 2 : ℝ) ^ (4 * b.2)) =
      ∑ b ∈ B, ((1 / 2 : ℝ) ^ 4) ^ b.2 := by
    simp only [pow_mul]
  rw [heq]
  exact lt_of_le_of_lt h (by norm_num)

/-- Large weights can be bought outright at a total factor of at most `1/64`. -/
theorem outright_weight_le {r : ℕ} {q w : ℝ} (hr : 1 ≤ r) (hq : 0 ≤ q)
    (hw : (1 / 2 : ℝ) ^ (64 * r) ≤ w) :
    (q / (2 : ℝ) ^ 70) ^ r ≤ (1 / 64 : ℝ) * q ^ r * w := by
  have hsmall : (1 / 2 : ℝ) ^ (6 * r) ≤ (1 / 64 : ℝ) := by
    have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (show 6 ≤ 6 * r by omega)
    norm_num at h ⊢
    exact h
  have hqpow : 0 ≤ q ^ r := pow_nonneg hq _
  calc
    (q / (2 : ℝ) ^ 70) ^ r = q ^ r * (1 / 2 : ℝ) ^ (70 * r) := by
      simp only [div_eq_mul_inv, mul_pow, one_mul, pow_mul, inv_pow]
    _ = q ^ r * ((1 / 2 : ℝ) ^ (6 * r) * (1 / 2 : ℝ) ^ (64 * r)) := by
      rw [← pow_add, show 6 * r + 64 * r = 70 * r by omega]
    _ ≤ q ^ r * ((1 / 64 : ℝ) * w) := by
      apply mul_le_mul_of_nonneg_left _ hqpow
      exact mul_le_mul hsmall hw (by positivity) (by norm_num)
    _ = (1 / 64 : ℝ) * q ^ r * w := by ring

/-- The lower edge of a bin bounds its cardinality at the reduced density. -/
theorem bin_card_cost_bound {n r h : ℕ} {q : ℝ} (hq : 0 < q)
    (hw : (n : ℝ) * q ^ r * (1 / 2 : ℝ) ^ (h + 1) ≤ 1) :
    (n : ℝ) * (q / (2 : ℝ) ^ 70) ^ r ≤ (2 : ℝ) ^ (h + 1) := by
  have hrho : q / (2 : ℝ) ^ 70 ≤ q := div_le_self hq.le (by norm_num)
  have hden : (1 / 2 : ℝ) ^ (h + 1) * (2 : ℝ) ^ (h + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (n : ℝ) * (q / (2 : ℝ) ^ 70) ^ r ≤ (n : ℝ) * q ^ r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrho r) (by positivity)
    _ = ((n : ℝ) * q ^ r * (1 / 2 : ℝ) ^ (h + 1)) * (2 : ℝ) ^ (h + 1) := by
      calc
        (n : ℝ) * q ^ r = ((n : ℝ) * q ^ r) *
            ((1 / 2 : ℝ) ^ (h + 1) * (2 : ℝ) ^ (h + 1)) := by rw [hden, mul_one]
        _ = _ := by ring
    _ ≤ 1 * (2 : ℝ) ^ (h + 1) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ = (2 : ℝ) ^ (h + 1) := one_mul _

/-- Fewer than `2^(12h)` weights at most `2⁻ʰ` have small sixteenth-power sum. -/
theorem bin_power_bound {m h : ℕ} (hm : m ≤ 2 ^ (12 * h)) :
    (m : ℝ) * ((1 / 2 : ℝ) ^ h) ^ 16 ≤ (1 / 2 : ℝ) ^ (4 * h) := by
  have hm' : (m : ℝ) ≤ (2 : ℝ) ^ (12 * h) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hm
  calc
    (m : ℝ) * ((1 / 2 : ℝ) ^ h) ^ 16 ≤
        (2 : ℝ) ^ (12 * h) * ((1 / 2 : ℝ) ^ h) ^ 16 :=
      mul_le_mul_of_nonneg_right hm' (by positivity)
    _ = (1 / 2 : ℝ) ^ (4 * h) := by
      rw [← pow_mul, show h * 16 = 12 * h + 4 * h by omega,
        pow_add, ← mul_assoc, ← mul_pow]
      norm_num

end TalagrandDiscreteConvexity

end OAI
