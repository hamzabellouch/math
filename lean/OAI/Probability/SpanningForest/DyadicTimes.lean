import Mathlib

namespace OAI

noncomputable section

open Filter
open scoped Topology NNReal

namespace Problem336.DyadicTimes

def grid (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (2 : ℝ≥0) ^ n

def enumeration (i : ℕ) : ℝ≥0 := grid (Nat.unpair i).1 (Nat.unpair i).2

@[simp] theorem enumeration_pair (n k : ℕ) : enumeration (Nat.pair n k) = grid n k := by
  simp [enumeration]

@[simp] theorem enumeration_zero : enumeration 0 = 0 := by
  norm_num [enumeration, grid, Nat.unpair]

@[simp] theorem coe_grid (n k : ℕ) :
    (grid n k : ℝ) = (k : ℝ) / (2 : ℝ) ^ n := by
  simp [grid]

@[simp] theorem grid_zero (n : ℕ) : grid n 0 = 0 := by simp [grid]

@[simp] theorem grid_level_zero (k : ℕ) : grid 0 k = k := by simp [grid]

lemma grid_refine_even (n k : ℕ) : grid (n + 1) (2 * k) = grid n k := by
  apply NNReal.coe_injective
  simp only [coe_grid, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp

lemma grid_refine_midpoint (n k : ℕ) :
    (grid (n + 1) (2 * k + 1) : ℝ) =
      ((grid n k : ℝ) + (grid n (k + 1) : ℝ)) / 2 := by
  simp only [coe_grid, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, pow_succ]
  field_simp
  ring

lemma grid_increment (n k : ℕ) :
    (grid n (k + 1) : ℝ) - (grid n k : ℝ) = ((2 : ℝ) ^ n)⁻¹ := by
  simp only [coe_grid, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

lemma grid_le_one_iff (n k : ℕ) : grid n k ≤ 1 ↔ k ≤ 2 ^ n := by
  change (grid n k : ℝ) ≤ (1 : ℝ) ↔ k ≤ 2 ^ n
  rw [coe_grid, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n), one_mul]
  exact_mod_cast (Iff.rfl : k ≤ 2 ^ n ↔ k ≤ 2 ^ n)

def approximant (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  grid n ⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊

lemma approximant_le (n : ℕ) (t : ℝ≥0) : approximant n t ≤ t := by
  change (approximant n t : ℝ) ≤ (t : ℝ)
  simp only [approximant, coe_grid]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).2
  exact Nat.floor_le (mul_nonneg t.2 (by positivity))

lemma sub_approximant_nonneg (n : ℕ) (t : ℝ≥0) :
    0 ≤ (t : ℝ) - approximant n t :=
  sub_nonneg.mpr (show (approximant n t : ℝ) ≤ (t : ℝ) from approximant_le n t)

lemma sub_approximant_lt (n : ℕ) (t : ℝ≥0) :
    (t : ℝ) - approximant n t < ((2 : ℝ) ^ n)⁻¹ := by
  have hp : 0 < (2 : ℝ) ^ n := by positivity
  have hfloor := Nat.lt_floor_add_one ((t : ℝ) * (2 : ℝ) ^ n)
  simp only [approximant, coe_grid]
  apply (mul_lt_mul_iff_left₀ hp).mp
  field_simp
  nlinarith

lemma tendsto_approximant (t : ℝ≥0) :
    Tendsto (fun n => approximant n t) atTop (nhds t) := by
  apply NNReal.tendsto_coe.mp
  change Tendsto (fun n : ℕ => (⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊ : ℝ) / (2 : ℝ) ^ n)
    atTop (nhds (t : ℝ))
  exact (tendsto_nat_floor_mul_div_atTop t.2).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

lemma approximant_mem_range (n : ℕ) (t : ℝ≥0) :
    approximant n t ∈ Set.range enumeration := by
  exact ⟨Nat.pair n ⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊, enumeration_pair _ _⟩

theorem denseRange_enumeration : DenseRange enumeration := by
  intro t
  exact mem_closure_of_tendsto (tendsto_approximant t)
    (Filter.Eventually.of_forall (fun n => approximant_mem_range n t))

end Problem336.DyadicTimes

end

end OAI
