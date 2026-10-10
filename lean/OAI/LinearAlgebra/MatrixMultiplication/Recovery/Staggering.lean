import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.Staggering

abbrev Capacity := Fin 3 → ℝ

def totalCapacity (a b : Capacity) (base : ℝ) : ℝ :=
  base + (∑ i, (a i + b i)) / 3

def balanceFraction (a b : Capacity) (high base : ℝ) (i : Fin 3) : ℝ :=
  (high - totalCapacity a b base + (a i + b i)) / (3 * (high - base))

def thirdCapacity (a b : Capacity) (high base : ℝ) (i : Fin 3) : ℝ :=
  high - 3 * balanceFraction a b high base i * (high - base)

theorem balanceFraction_pos (a b : Capacity) (high base : ℝ)
    (hbase : base < high)
    (hfeas : ∀ i, totalCapacity a b base - (a i + b i) < high) (i : Fin 3) :
    0 < balanceFraction a b high base i := by
  apply div_pos
  · linarith [hfeas i]
  · exact mul_pos (by norm_num) (sub_pos.mpr hbase)

theorem sum_balanceFraction (a b : Capacity) (high base : ℝ)
    (hbase : base < high) : ∑ i, balanceFraction a b high base i = 1 := by
  have hn : high - base ≠ 0 := ne_of_gt (sub_pos.mpr hbase)
  simp only [balanceFraction, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  unfold totalCapacity
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  field_simp
  ring

theorem thirdCapacity_eq (a b : Capacity) (high base : ℝ)
    (hbase : base < high) (i : Fin 3) :
    thirdCapacity a b high base i = totalCapacity a b base - (a i + b i) := by
  have hn : high - base ≠ 0 := ne_of_gt (sub_pos.mpr hbase)
  unfold thirdCapacity balanceFraction
  field_simp
  ring

theorem balanced (a b : Capacity) (high base : ℝ) (hbase : base < high)
    (i : Fin 3) : a i + b i + thirdCapacity a b high base i =
      totalCapacity a b base := by
  rw [thirdCapacity_eq a b high base hbase]
  ring

def minCapacity (a : Capacity) : ℝ := min (a 0) (min (a 1) (a 2))

def maxCapacity (a : Capacity) : ℝ := max (a 0) (max (a 1) (a 2))

theorem minCapacity_pos (a : Capacity) (h : ∀ i, 0 < a i) :
    0 < minCapacity a := by
  exact lt_min (h 0) (lt_min (h 1) (h 2))

theorem minCapacity_le_maxCapacity (a : Capacity) : minCapacity a ≤ maxCapacity a := by
  exact (min_le_left _ _).trans (le_max_left _ _)

theorem minCapacity_complement (a : Capacity) (c : ℝ) :
    minCapacity (fun i => c - a i) = c - maxCapacity a := by
  simp only [minCapacity, maxCapacity, min_def, max_def]
  split_ifs <;> linarith

def boundaryDeficit (a b c : Capacity) (full : ℝ) : ℝ :=
  2 * full - minCapacity a - minCapacity (fun i => a i + b i) -
    minCapacity (fun i => b i + c i) - minCapacity c

theorem boundaryDeficit_eq_ranges (a b c : Capacity) (full : ℝ)
    (h : ∀ i, a i + b i + c i = full) :
    boundaryDeficit a b c full =
      (maxCapacity a - minCapacity a) + (maxCapacity c - minCapacity c) := by
  have hab : (fun i => a i + b i) = (fun i => full - c i) := by
    funext i
    linarith [h i]
  have hbc : (fun i => b i + c i) = (fun i => full - a i) := by
    funext i
    linarith [h i]
  rw [boundaryDeficit, hab, hbc, minCapacity_complement, minCapacity_complement]
  ring

theorem boundaryDeficit_nonneg (a b c : Capacity) (full : ℝ)
    (h : ∀ i, a i + b i + c i = full) : 0 ≤ boundaryDeficit a b c full := by
  rw [boundaryDeficit_eq_ranges a b c full h]
  exact add_nonneg (sub_nonneg.mpr (minCapacity_le_maxCapacity a))
    (sub_nonneg.mpr (minCapacity_le_maxCapacity c))

theorem finite_schedule_yield (a b c : Capacity) (full : ℝ) (K : ℕ) (hK : 2 ≤ K) :
    (K - 2 : ℕ) * full + minCapacity a + minCapacity (fun i => a i + b i) +
      minCapacity (fun i => b i + c i) + minCapacity c =
      (K : ℝ) * full - boundaryDeficit a b c full := by
  rw [Nat.cast_sub hK]
  norm_num [boundaryDeficit]
  ring

theorem physical_order_unique (rho sigma : Equiv.Perm (Fin 3)) :
    ∃! phi : Equiv.Perm (Fin 3), rho.trans phi = sigma := by
  refine ⟨rho.symm.trans sigma, ?_, ?_⟩
  · ext i
    simp
  · intro phi hphi
    apply Equiv.ext
    intro i
    have h := Equiv.congr_fun hphi (rho.symm i)
    simpa using h

end MatrixMultiplication.Staggering

end

end OAI
