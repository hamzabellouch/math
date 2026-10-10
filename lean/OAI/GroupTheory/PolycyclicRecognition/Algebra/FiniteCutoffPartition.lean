import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizePositiveMass
import Mathlib.Analysis.Normed.Lp.PiLp

namespace OAI

/-! # The quantitative cutoff partition used by Lipschitz replacement -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {X I : Type*} [MetricSpace X] [Fintype I]

/-- Unnormalized radius-two distance cutoffs in the sum norm. -/
def cutoffMass (v : I → X) (x : X) : PiLp 1 (fun _ : I => ℝ) :=
  WithLp.toLp 1 (fun i => max 0 (2 - dist x (v i)))

def cutoffPartition (v : I → X) (x : X) : PiLp 1 (fun _ : I => ℝ) :=
  ‖cutoffMass v x‖⁻¹ • cutoffMass v x

private theorem cutoff_difference_le (v x y : X) :
    |max 0 (2 - dist x v) - max 0 (2 - dist y v)| ≤ dist x y := by
  have hd := abs_le.mp (abs_dist_sub_le x y v)
  simp only [max_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith [dist_nonneg (x := x) (y := y)]

/-- Before normalization, at most one distance error is charged per
participating center. The application restricts to the finite local support. -/
theorem norm_cutoffMass_sub_le (v : I → X) (x y : X) :
    ‖cutoffMass v x - cutoffMass v y‖ ≤ (Fintype.card I : ℝ) * dist x y := by
  rw [PiLp.norm_eq_of_L1]
  change (∑ i, |max 0 (2 - dist x (v i)) - max 0 (2 - dist y (v i))|) ≤ _
  calc
    _ ≤ ∑ _i : I, dist x y := Finset.sum_le_sum (fun i _ => cutoff_difference_le (v i) x y)
    _ = _ := by simp

/-- The unit-ball cover gives the uniform lower bound on the denominator. -/
theorem one_le_norm_cutoffMass (v : I → X) (x : X)
    (hcover : ∃ i, dist x (v i) ≤ 1) : 1 ≤ ‖cutoffMass v x‖ := by
  obtain ⟨i, hi⟩ := hcover
  rw [PiLp.norm_eq_of_L1]
  change 1 ≤ ∑ j, ‖max 0 (2 - dist x (v j))‖
  calc
    1 ≤ max 0 (2 - dist x (v i)) := (by linarith : 1 ≤ 2 - dist x (v i)).trans (le_max_right _ _)
    _ = ‖max 0 (2 - dist x (v i))‖ := (Real.norm_of_nonneg (le_max_left _ _)).symm
    _ ≤ _ := Finset.single_le_sum (fun j _ => norm_nonneg (max 0 (2 - dist x (v j)))) (Finset.mem_univ i)

/-- Normalization costs a factor two, uniformly over points whose unit
balls contain one of the participating centers. -/
theorem norm_cutoffPartition_sub_le (v : I → X) (x y : X)
    (hx : ∃ i, dist x (v i) ≤ 1) (hy : ∃ i, dist y (v i) ≤ 1) :
    ‖cutoffPartition v x - cutoffPartition v y‖ ≤
      2 * (Fintype.card I : ℝ) * dist x y := by
  exact (norm_normalized_sub_le_two (cutoffMass v x) (cutoffMass v y)
    (one_le_norm_cutoffMass v x hx) (one_le_norm_cutoffMass v y hy)).trans
    (by nlinarith only [norm_cutoffMass_sub_le v x y])

/-- These are genuine barycentric coordinates, with nonnegative entries
and total mass exactly one. -/
theorem cutoffPartition_probability (v : I → X) (x : X)
    (hcover : ∃ i, dist x (v i) ≤ 1) :
    (∀ i, 0 ≤ cutoffPartition v x i) ∧ (∑ i, cutoffPartition v x i) = 1 := by
  have hpos : 0 < ‖cutoffMass v x‖ := lt_of_lt_of_le zero_lt_one (one_le_norm_cutoffMass v x hcover)
  have hn : ‖cutoffMass v x‖ = ∑ i, max 0 (2 - dist x (v i)) := by
    rw [PiLp.norm_eq_of_L1]
    exact Finset.sum_congr rfl (fun i _ => Real.norm_of_nonneg (le_max_left _ _))
  constructor
  · intro i
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (le_max_left _ _)
  · change (∑ i, ‖cutoffMass v x‖⁻¹ * max 0 (2 - dist x (v i))) = 1
    rw [← Finset.mul_sum, ← hn, inv_mul_cancel₀ hpos.ne']

end PolycyclicRecognition

end

end OAI
