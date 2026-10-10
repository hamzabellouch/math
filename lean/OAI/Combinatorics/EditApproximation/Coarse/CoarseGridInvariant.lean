import OAI.Combinatorics.EditApproximation.Coarse.CoarsePrecision
import OAI.Combinatorics.EditApproximation.Coarse.CoarseGlobalSeed

namespace OAI

namespace EditApproximation

/-- One descended allowance acquires only one factor of the fixed root
base in its denominator. This includes the literal sampled child label. -/
 theorem coarseChildAllowance_grid (B q L j : ℕ) (allowance : ℚ) (draw : Fin B)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (ha : allowance.den ∣ (L * B * q) ^ j) :
    ((1 / (L : ℚ)) * coarseChildThreshold B q allowance draw).den ∣
      (L * B * q) ^ (j + 1) := by
  have ht : (coarseChildThreshold B q allowance draw).den ∣
      (L * B * q) ^ j * (B * q) := by
    simpa only [coarseChildThreshold, Nat.cast_mul] using
      coarse_rat_div_nat_den_dvd (allowance * ((draw.val + 1 : ℕ) : ℚ)) (B * q) ((L * B * q) ^ j)
        (Nat.mul_pos hB hq) (coarse_rat_mul_nat_den_dvd allowance (draw.val + 1) _ ha)
  have heq : (1 / (L : ℚ)) * coarseChildThreshold B q allowance draw =
      coarseChildThreshold B q allowance draw / L := by ring
  rw [heq]
  convert coarse_rat_div_nat_den_dvd _ L _ hL ht using 1
  rw [pow_succ]
  ring

/-- Every descendant array lives on the same denominator constructed for
its root; it is unnecessary to normalize any array sum by a gcd. -/
 theorem coarseDescendant_grid {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L j : ℕ) (frame : List (Option α)) (tree : CoarseSourceTree B α d)
    (draws : CoarseThresholdDraws B d) (allowance : ℚ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (ha : allowance.den ∣ (L * B * q) ^ j) (start : ℕ) (shift : Fin (2 * k + 1)) :
    (coarseThresholdEstimate k q (1 / L) frame tree draws allowance start shift).den ∣
      coarseCommonDenominator 1 q L B (j + d) := by
  have h := coarseThresholdEstimate_den_dvd k q L frame tree draws allowance
    ((L * B * q) ^ j) hB hq hL (pow_pos (by positivity) _) ha start shift
  convert h using 1
  simp only [coarseCommonDenominator, one_mul, pow_add]
  ring

/-- Uniform root magnitude for every descendant and pruning outcome. -/
 theorem coarseDescendant_magnitude {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L D n : ℕ) (frame : List (Option α)) (tree : CoarseSourceTree B α d)
    (draws : CoarseThresholdDraws B d) (allowance : ℚ)
    (hB : 2 ≤ B) (hq : 0 < q) (hL : 0 < L) (hd : d ≤ D)
    (hn : tree.word.length ≤ n) (ha : 0 ≤ allowance) (hak : allowance ≤ k)
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    |coarseThresholdEstimate k q (1 / L) frame tree draws allowance start shift| ≤
      ((n + B * k * B ^ D : ℕ) : ℚ) := by
  have hqQ : (1 : ℚ) ≤ q := by exact_mod_cast hq
  have hLQ : (1 : ℚ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℚ) < L := by exact_mod_cast hL
  have hnode : coarseInternalNodes B d ≤ B ^ D :=
    (Nat.le_of_succ_le (coarseInternalNodes_add_one_le_pow B d hB)).trans
      (Nat.pow_le_pow_right (by omega) hd)
  have hm := coarseThresholdEstimate_magnitude k q (1 / L) frame tree draws allowance hqQ
    (by positivity) ((div_le_one hLpos).mpr hLQ) ha start shift
  rw [abs_of_nonneg (coarseThresholdEstimate_nonneg k q (1 / L) frame tree draws allowance start shift
    (by positivity) ha)]
  apply hm.trans
  have hs : (B : ℚ) * allowance / q ≤ B * k := by
    exact (div_le_self (by positivity) hqQ).trans
      (mul_le_mul_of_nonneg_left hak (by positivity))
  have hh := mul_le_mul hs (by exact_mod_cast hnode : (coarseInternalNodes B d : ℚ) ≤ B ^ D)
    (by positivity) (by positivity : (0 : ℚ) ≤ B * k)
  push_cast
  exact add_le_add (by exact_mod_cast hn) hh

end EditApproximation

end OAI
