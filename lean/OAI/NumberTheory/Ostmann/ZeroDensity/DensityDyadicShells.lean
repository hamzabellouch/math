import Mathlib.Analysis.SpecificLimits.Basic
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFatou

namespace OAI

/-! # A disjoint dyadic decomposition of the whole height line -/

namespace Ostmann

open Set Filter
open scoped Topology

noncomputable def densityHeightBall (T : ℝ) (j : ℕ) : Set ℝ :=
  Icc (-((2 : ℝ) ^ j * T)) ((2 : ℝ) ^ j * T)

noncomputable def densityHeightShell (T : ℝ) : ℕ → Set ℝ
  | 0 => densityHeightBall T 0
  | j + 1 => densityHeightBall T (j + 1) \ densityHeightBall T j

 theorem densityHeightBall_mem (T : ℝ) (j : ℕ) (x : ℝ) :
    x ∈ densityHeightBall T j ↔ |x| ≤ (2 : ℝ) ^ j * T := by
  exact abs_le.symm

 theorem densityHeightBall_mono (T : ℝ) (hT : 0 ≤ T) {i j : ℕ} (hij : i ≤ j) :
    densityHeightBall T i ⊆ densityHeightBall T j := by
  intro x hx
  rw [densityHeightBall_mem] at hx ⊢
  exact hx.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hij) hT)

 theorem densityHeightShell_measurable (T : ℝ) (j : ℕ) : MeasurableSet (densityHeightShell T j) := by
  cases j with
  | zero => exact measurableSet_Icc
  | succ j => exact measurableSet_Icc.diff measurableSet_Icc

 theorem densityHeightShell_subset (T : ℝ) (j : ℕ) :
    densityHeightShell T j ⊆ densityHeightBall T j := by
  cases j with
  | zero => exact Set.Subset.rfl
  | succ j => exact Set.sdiff_subset

 theorem densityHeightShell_disjoint (T : ℝ) (hT : 0 ≤ T) :
    Pairwise (fun i j => Disjoint (densityHeightShell T i) (densityHeightShell T j)) := by
  have hd (i j : ℕ) (hij : i < j) : Disjoint (densityHeightShell T i) (densityHeightShell T j) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hy.2 (densityHeightBall_mono T hT (by omega) (densityHeightShell_subset T i hx))
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hd i j h
  · exact (hd j i h).symm

 theorem densityHeightShell_cover (T : ℝ) (hT : 0 < T) :
    (⋃ j : ℕ, densityHeightShell T j) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hex : ∃ j : ℕ, |x| ≤ (2 : ℝ) ^ j * T := by
    have ht : Tendsto (fun j : ℕ => (2 : ℝ) ^ j * T) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hT
    obtain ⟨j, hj⟩ := (ht.eventually (eventually_ge_atTop |x|)).exists
    exact ⟨j, hj⟩
  let j := Nat.find hex
  have hj : |x| ≤ (2 : ℝ) ^ j * T := Nat.find_spec hex
  apply Set.mem_iUnion.mpr
  refine ⟨j, ?_⟩
  cases he : j with
  | zero => exact (densityHeightBall_mem T 0 x).mpr (by simpa only [he] using hj)
  | succ k =>
    change x ∈ densityHeightBall T (k + 1) \ densityHeightBall T k
    refine ⟨(densityHeightBall_mem T (k + 1) x).mpr (by simpa only [he] using hj), ?_⟩
    rw [densityHeightBall_mem]
    exact Nat.find_min hex (by omega : k < Nat.find hex)

end Ostmann

end OAI
