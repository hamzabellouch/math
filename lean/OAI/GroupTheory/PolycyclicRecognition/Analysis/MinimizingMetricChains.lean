import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearMetricChains
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-! # Metric chains supplied by the chosen minimizing paths -/

noncomputable section
namespace PolycyclicRecognition

open Metric Set

/-- Sampling the chosen minimizing paths gives the concrete chain witnesses
needed by the canonical-height and proper-homomorphism metric bridges. -/
def linearMetricChains_of_minimizing_paths
    {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|) :
    LinearMetricChains G := by
  refine {
    step := 1
    step_pos := zero_lt_one
    slope := 1
    slope_nonneg := zero_le_one
    error := 1
    error_nonneg := zero_le_one
    chain := ?_ }
  intro x y
  obtain ⟨γ, h0, h1, hγ⟩ := hpath (x⁻¹ * y)
  let n := ⌊dist 1 (x⁻¹ * y)⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlen : dist 1 (x⁻¹ * y) ≤ (n : ℝ) := by
    simpa [n] using (Nat.lt_floor_add_one (dist 1 (x⁻¹ * y))).le
  let p : ℕ → G := fun k => x * γ ((k : ℝ) / n)
  refine ⟨n, p, ?_, ?_, ?_, ?_⟩
  · simp [p, h0]
  · simp [p, h1, hnr.ne']
  · simpa only [n, Nat.cast_add, Nat.cast_one, dist_one_groupDifference, one_mul, add_comm]
      using add_le_add_right (Nat.floor_le (dist_nonneg (x := (1 : G))
        (y := x⁻¹ * y))) 1
  · intro k hk
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk.le
    have hks : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk
    have ht : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr hkn⟩
    have hu : ((k + 1 : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr hks⟩
    have hdiff : |(k : ℝ) / n - ((k + 1 : ℕ) : ℝ) / n| = 1 / n := by
      rw [abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_right (by simp) hnr.le))]
      push_cast
      ring
    change dist (x * γ _) (x * γ _) ≤ 1
    rw [dist_mul_left]
    refine (hγ _ ht _ hu).trans ?_
    rw [hdiff, mul_one_div]
    exact (div_le_one hnr).mpr hlen

end PolycyclicRecognition

end

end OAI
