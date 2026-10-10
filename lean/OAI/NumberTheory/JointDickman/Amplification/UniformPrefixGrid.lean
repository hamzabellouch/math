import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicBoundaryWidths
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Uniform prefix control from a finite mesh of counting endpoints -/
namespace JointDickman
open Finset Filter
open scoped Topology

lemma norm_prefix_interval_le (f : ℕ → ℂ) {C a b : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n‖ ≤ C * (b - a + 1) := by
  calc
    _ ≤ ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, C := sum_le_sum (fun n _ => hf n)
    _ = C * ((Ioc ⌊a⌋₊ ⌊b⌋₊).card : ℝ) := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (nat_interval_card_le_length ha hab) hC

/-- No positivity of the coefficients is needed: bounded increments and a
finite mesh suffice for uniformity of their complex prefix sums. -/
theorem prefix_grid_uniform_bound (f : ℕ → ℂ) {C d D : ℝ} (N : ℕ)
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (hd : 0 < d)
    (hgrid : ∀ j ≤ N, ‖∑ n ∈ Ioc 0 ⌊(j : ℝ) * d⌋₊, f n‖ ≤ D)
    {u : ℝ} (hu : u ∈ Set.Icc 0 ((N : ℝ) * d)) :
    ‖∑ n ∈ Ioc 0 ⌊u⌋₊, f n‖ ≤ D + C * (d + 1) := by
  let j := ⌊u / d⌋₊
  have hur : 0 ≤ u / d := div_nonneg hu.1 hd.le
  have hjN : j ≤ N := by
    apply Nat.floor_le_of_le
    exact (div_le_iff₀ hd).mpr hu.2
  have hjlo : (j : ℝ) * d ≤ u := by
    have hh := Nat.floor_le hur
    exact (le_div_iff₀ hd).mp hh
  have hjhi : u ≤ (j : ℝ) * d + d := by
    have hh := Nat.lt_floor_add_one (u / d)
    have hh' := (div_lt_iff₀ hd).mp hh
    linarith
  have hj0 : 0 ≤ (j : ℝ) * d := by positivity
  have hsplit : (∑ n ∈ Ioc 0 ⌊u⌋₊, f n) =
      (∑ n ∈ Ioc 0 ⌊(j : ℝ) * d⌋₊, f n) +
        (∑ n ∈ Ioc ⌊(j : ℝ) * d⌋₊ ⌊u⌋₊, f n) := by
    rw [← Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (Nat.floor_mono hjlo),
      sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  rw [hsplit]
  calc
    _ ≤ ‖∑ n ∈ Ioc 0 ⌊(j : ℝ) * d⌋₊, f n‖ +
        ‖∑ n ∈ Ioc ⌊(j : ℝ) * d⌋₊ ⌊u⌋₊, f n‖ := norm_add_le _ _
    _ ≤ D + C * (u - (j : ℝ) * d + 1) :=
      add_le_add (hgrid j hjN) (norm_prefix_interval_le f hC hf hj0 hjlo)
    _ ≤ _ := by gcongr; linarith

end JointDickman

end OAI
