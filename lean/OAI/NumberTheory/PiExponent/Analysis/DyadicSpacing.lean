import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.FieldSimp
import OAI.NumberTheory.PiExponent.Analysis.DyadicPowers
import OAI.NumberTheory.PiExponent.Analysis.DyadicSummation
import OAI.NumberTheory.PiExponent.Analysis.FiniteSpacing
import OAI.NumberTheory.PiExponent.Analysis.FlintHills

namespace OAI

noncomputable section

open scoped BigOperators

namespace PiExponent

def centeredResidue (alpha : ℝ) (q : ℕ) : ℝ :=
  (q : ℝ) * alpha - (round ((q : ℝ) * alpha) : ℝ)

theorem abs_centeredResidue (alpha : ℝ) (q : ℕ) :
    |centeredResidue alpha q| = integerDistance ((q : ℝ) * alpha) := rfl

theorem integerDistance_sub_le (x y : ℝ) :
    integerDistance (x - y) ≤ |(x - (round x : ℝ)) - (y - (round y : ℝ))| := by
  have h := integerDistance_le (x - y) (round x - round y)
  push_cast at h
  convert h using 1
  congr 1
  ring

theorem centeredResidue_separation {alpha c nu : ℝ} (hc : 0 < c) (hnu : 1 < nu)
    (hlower : ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - nu) ≤ integerDistance ((q : ℝ) * alpha))
    {K q r : ℕ} (hq : q ∈ Finset.Ico K (2 * K))
    (hr : r ∈ Finset.Ico K (2 * K)) (hqr : q < r) :
    c * (2 * (K : ℝ)) ^ (1 - nu) ≤
      |centeredResidue alpha r - centeredResidue alpha q| := by
  have hdiff : 0 < r - q := Nat.sub_pos_of_lt hqr
  have hdiffR : (0 : ℝ) < (r - q : ℕ) := by exact_mod_cast hdiff
  have hdiffle : ((r - q : ℕ) : ℝ) ≤ 2 * (K : ℝ) := by
    have hqK := (Finset.mem_Ico.mp hq).1
    have hrK := (Finset.mem_Ico.mp hr).2
    have hlt : r - q < K := by omega
    exact_mod_cast hlt.le.trans (by omega : K ≤ 2 * K)
  have hpower := Real.rpow_le_rpow_of_nonpos hdiffR hdiffle (by linarith : 1 - nu ≤ 0)
  have hsep := integerDistance_sub_le ((r : ℝ) * alpha) ((q : ℝ) * alpha)
  have hcast : ((r - q : ℕ) : ℝ) * alpha = (r : ℝ) * alpha - (q : ℝ) * alpha := by
    rw [Nat.cast_sub hqr.le]
    ring
  calc
    c * (2 * (K : ℝ)) ^ (1 - nu) ≤ c * ((r - q : ℕ) : ℝ) ^ (1 - nu) :=
      mul_le_mul_of_nonneg_left hpower hc.le
    _ ≤ integerDistance (((r - q : ℕ) : ℝ) * alpha) := hlower (r - q) hdiff
    _ ≤ |centeredResidue alpha r - centeredResidue alpha q| := by
      rw [hcast]
      exact hsep

theorem integerDistance_block_lower {alpha c nu : ℝ} (hc : 0 < c) (hnu : 1 < nu)
    (hlower : ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - nu) ≤ integerDistance ((q : ℝ) * alpha))
    {K q : ℕ} (hK : 0 < K) (hq : q ∈ Finset.Ico K (2 * K)) :
    c * (2 * (K : ℝ)) ^ (1 - nu) ≤ integerDistance ((q : ℝ) * alpha) := by
  have hqpos : 0 < q := hK.trans_le (Finset.mem_Ico.mp hq).1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hqle : (q : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hq).2.le
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hqR hqle (by linarith : 1 - nu ≤ 0)) hc.le).trans
    (hlower q hqpos)

theorem integerDistance_block_sum {alpha c nu : ℝ} (hc : 0 < c) (hnu : 1 < nu)
    (hlower : ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - nu) ≤ integerDistance ((q : ℝ) * alpha))
    {K : ℕ} (hK : 0 < K) :
    (∑ q ∈ Finset.Ico K (2 * K), 1 / (integerDistance ((q : ℝ) * alpha)) ^ 2) ≤
      4 / (c * (2 * (K : ℝ)) ^ (1 - nu)) ^ 2 := by
  classical
  let rows := Finset.Ico K (2 * K)
  let d : ℝ := c * (2 * (K : ℝ)) ^ (1 - nu)
  have hd : 0 < d := by dsimp [d]; positivity
  have hmin : ∀ q ∈ rows, d ≤ integerDistance ((q : ℝ) * alpha) :=
    fun q hq => integerDistance_block_lower hc hnu hlower hK hq
  have hsep : ∀ q ∈ rows, ∀ r ∈ rows, q ≠ r →
      d ≤ |centeredResidue alpha q - centeredResidue alpha r| := by
    intro q hq r hr hqr
    rcases lt_or_gt_of_ne hqr with hqr | hrq
    · simpa only [abs_sub_comm] using centeredResidue_separation hc hnu hlower hq hr hqr
    · exact centeredResidue_separation hc hnu hlower hr hq hrq
  have hpos := FiniteSpacing.sum_inv_sq_le_two_div_sq_indexed
    (rows.filter fun q => 0 ≤ centeredResidue alpha q)
    (fun q => integerDistance ((q : ℝ) * alpha)) hd
    (fun q hq => hmin q (Finset.mem_filter.mp hq).1)
    (by
      intro q hq r hr hqr
      change d ≤ abs (abs (centeredResidue alpha q) - abs (centeredResidue alpha r))
      rw [abs_of_nonneg (Finset.mem_filter.mp hq).2,
        abs_of_nonneg (Finset.mem_filter.mp hr).2]
      exact hsep q (Finset.mem_filter.mp hq).1 r (Finset.mem_filter.mp hr).1 hqr)
  have hneg := FiniteSpacing.sum_inv_sq_le_two_div_sq_indexed
    (rows.filter fun q => ¬ 0 ≤ centeredResidue alpha q)
    (fun q => integerDistance ((q : ℝ) * alpha)) hd
    (fun q hq => hmin q (Finset.mem_filter.mp hq).1)
    (by
      intro q hq r hr hqr
      change d ≤ abs (abs (centeredResidue alpha q) - abs (centeredResidue alpha r))
      rw [abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hq).2),
        abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hr).2), neg_sub_neg, abs_sub_comm]
      exact hsep q (Finset.mem_filter.mp hq).1 r (Finset.mem_filter.mp hr).1 hqr)
  change (∑ q ∈ rows, 1 / (integerDistance ((q : ℝ) * alpha)) ^ 2) ≤ 4 / d ^ 2
  rw [← Finset.sum_filter_add_sum_filter_not rows (fun q => 0 ≤ centeredResidue alpha q)]
  calc
    _ ≤ 2 / d ^ 2 + 2 / d ^ 2 := add_le_add hpos hneg
    _ = _ := by ring

theorem inverse_cube_integerDistance_block_sum {alpha c nu : ℝ}
    (hc : 0 < c) (hnu : 1 < nu)
    (hlower : ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - nu) ≤ integerDistance ((q : ℝ) * alpha))
    {K : ℕ} (hK : 0 < K) :
    (∑ q ∈ Finset.Ico K (2 * K),
      1 / ((q : ℝ) ^ 3 * (integerDistance ((q : ℝ) * alpha)) ^ 2)) ≤
      4 / ((K : ℝ) ^ 3 * (c * (2 * (K : ℝ)) ^ (1 - nu)) ^ 2) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  calc
    _ ≤ ∑ q ∈ Finset.Ico K (2 * K),
        (1 / (K : ℝ) ^ 3) * (1 / (integerDistance ((q : ℝ) * alpha)) ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      have hKq : (K : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Ico.mp hq).1
      have hdist : 0 < integerDistance ((q : ℝ) * alpha) :=
        (mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)).trans_le
          (integerDistance_block_lower hc hnu hlower hK hq)
      rw [one_div_mul_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hKR.le hKq 3) (sq_nonneg _))
    _ = (1 / (K : ℝ) ^ 3) *
        ∑ q ∈ Finset.Ico K (2 * K), 1 / (integerDistance ((q : ℝ) * alpha)) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (K : ℝ) ^ 3) * (4 / (c * (2 * (K : ℝ)) ^ (1 - nu)) ^ 2) :=
      mul_le_mul_of_nonneg_left (integerDistance_block_sum hc hnu hlower hK) (by positivity)
    _ = _ := by ring

theorem summable_inverse_cube_integerDistance {alpha c nu : ℝ}
    (hc : 0 < c) (hnu1 : 1 < nu) (hnu2 : nu < 5 / 2)
    (hlower : ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - nu) ≤ integerDistance ((q : ℝ) * alpha)) :
    Summable (fun q : ℕ =>
      1 / ((q : ℝ) ^ 3 * (integerDistance ((q : ℝ) * alpha)) ^ 2)) := by
  apply summable_of_dyadic_blocks (fun q hq => by positivity)
    (summable_dyadic_block_bound hc hnu2)
  intro k
  have hblock := inverse_cube_integerDistance_block_sum hc hnu1 hlower
    (pow_pos (by norm_num : (0 : ℕ) < 2) k)
  have hend : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
  rw [hend] at hblock
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hblock

end PiExponent

end

end OAI
