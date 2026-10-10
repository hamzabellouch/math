import OAI.GroupTheory.PolycyclicRecognition.Algebra.CocycleGrowth
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-! # Word decompositions by sampling minimizing paths

This supplies the bounded-step word decomposition used in the stationary
estimate from actual metric paths. The number of steps is at most distance
plus one.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

/-- Subdivision of a minimizing path gives a word in the unit ball, with
length at most distance plus one. -/
theorem wordFactorization_of_minimizing_paths
    {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|) (g : G) :
    ∃ w : List G, (∀ q ∈ w, q ∈ closedBall 1 1) ∧ w.prod = g ∧
      (w.length : ℝ) ≤ dist 1 g + 1 := by
  obtain ⟨γ, h0, h1, hγ⟩ := hpath g
  let n := ⌊dist 1 g⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlen : dist 1 g ≤ (n : ℝ) := by
    simpa [n] using (Nat.lt_floor_add_one (dist 1 g)).le
  let v : ℕ → G := fun k => γ ((k : ℝ) / n)
  let w := (List.range n).map (fun k => (v k)⁻¹ * v (k + 1))
  refine ⟨w, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
    have hk' : k < n := List.mem_range.mp hk
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk'.le
    have hks : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk'
    have ht : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr hkn⟩
    have hu : ((k + 1 : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr hks⟩
    have hdiff : |(k : ℝ) / n - ((k + 1 : ℕ) : ℝ) / n| = 1 / n := by
      rw [abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_right (by simp) hnr.le))]
      push_cast
      ring
    have hd : dist 1 ((v k)⁻¹ * v (k + 1)) = dist (v k) (v (k + 1)) := by
      simpa using (dist_mul_left (v k) (1 : G) ((v k)⁻¹ * v (k + 1))).symm
    rw [mem_closedBall, dist_comm, hd]
    refine (hγ _ ht _ hu).trans ?_
    rw [hdiff, mul_one_div]
    exact (div_le_one hnr).mpr hlen
  · have hp := List.prod_range_div' n (fun k => (v k)⁻¹)
    have hv0 : v 0 = 1 := by simp [v, h0]
    have hvn : v n = g := by simp [v, h1, hnr.ne']
    simpa [w, div_eq_mul_inv, hv0, hvn] using hp
  · simpa [w, n, Nat.cast_add, Nat.cast_one] using
      add_le_add_right (Nat.floor_le (dist_nonneg (x := (1 : G)) (y := g))) 1

end PolycyclicRecognition

end

end OAI
