import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.NetAncestors
import OAI.Analysis.RieszRectifiability.Foundations.GeometricGramRows

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set Filter Topology

def latticeRadius (R : ℝ) (k : ℕ) : ℝ := R * (1 / 64 : ℝ) ^ k

theorem latticeRadius_zero (R : ℝ) : latticeRadius R 0 = R := by simp [latticeRadius]

theorem latticeRadius_pos (R : ℝ) (hR : 0 < R) (k : ℕ) : 0 < latticeRadius R k := by
  unfold latticeRadius
  positivity

theorem latticeRadius_succ (R : ℝ) (k : ℕ) : latticeRadius R (k + 1) = latticeRadius R k / 64 := by
  unfold latticeRadius
  rw [pow_succ]
  ring

theorem latticeRadius_add (R : ℝ) (k t : ℕ) :
    latticeRadius R (k + t) = latticeRadius R k * (1 / 64 : ℝ) ^ t := by
  simp only [latticeRadius, pow_add, mul_assoc]

theorem latticeRadius_antitone (R : ℝ) (hR : 0 ≤ R) : Antitone (latticeRadius R) := by
  intro k l hkl
  unfold latticeRadius
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hkl) hR

theorem latticeRadius_tendsto_zero (R : ℝ) : Tendsto (latticeRadius R) atTop (𝓝 0) := by
  simpa only [mul_zero] using!
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 64)
      (by norm_num : (1 / 64 : ℝ) < 1)).const_mul R

theorem latticeRadius_binary_levels (R : ℝ) (k : ℕ) :
    latticeRadius R k = R * (1 / 2 : ℝ) ^ (6 * k) := by
  unfold latticeRadius
  rw [pow_mul]
  norm_num

theorem latticeRadius_sum_le (R : ℝ) (hR : 0 ≤ R) (k t : ℕ) :
    ∑ j ∈ Finset.range t, latticeRadius R (k + j) ≤ 2 * latticeRadius R k := by
  simp_rw [latticeRadius_add]
  rw [← Finset.mul_sum]
  have hpow : (∑ j ∈ Finset.range t, (1 / 64 : ℝ) ^ j) ≤ 2 :=
    (Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (by norm_num) (by norm_num) j)).trans
      (finite_geometric_two_sum_le (Finset.range t))
  have hk : 0 ≤ latticeRadius R k := by unfold latticeRadius; positivity
  simpa only [mul_comm] using! mul_le_mul_of_nonneg_left hpow hk

theorem netAncestor_dist_le_latticeRadius {X : Type*} [MetricSpace X] {E : Set X}
    (R : ℝ) (hR : 0 < R) (N : (k : ℕ) → SeparatedCover E (latticeRadius R k))
    (k t : ℕ) (x : E) : dist (x : X) (netAncestor N k t x : X) ≤ 2 * latticeRadius R k :=
  (netAncestor_dist_le_sum N (latticeRadius_pos R hR) k t x).trans
    (latticeRadius_sum_le R hR.le k t)

end

end RieszRectifiability

end OAI
