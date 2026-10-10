import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

namespace WeakHessian

def triangularFold (δ x : ℝ) : ℝ :=
  Metric.infDist x (Set.range fun k : ℤ => δ * (k : ℝ))

lemma triangularFold_lipschitz (δ : ℝ) : LipschitzWith 1 (triangularFold δ) :=
  Metric.lipschitz_infDist_pt _

lemma triangularFold_zero (δ : ℝ) : triangularFold δ 0 = 0 := by
  apply Metric.infDist_zero_of_mem
  exact ⟨0, by simp⟩

lemma triangularFold_nonneg (δ x : ℝ) : 0 ≤ triangularFold δ x :=
  Metric.infDist_nonneg

lemma triangularFold_eq_round {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    triangularFold δ x = |x - δ * (round (x / δ) : ℝ)| := by
  unfold triangularFold
  apply le_antisymm
  · simpa only [Real.dist_eq] using
      Metric.infDist_le_dist_of_mem (x := x) (Set.mem_range_self (round (x / δ)))
  · apply (Metric.le_infDist (Set.range_nonempty (fun k : ℤ => δ * (k : ℝ)))).2
    rintro y ⟨k, rfl⟩
    have H := mul_le_mul_of_nonneg_left (round_le (x / δ) k) (abs_nonneg δ)
    rw [← abs_mul, ← abs_mul] at H
    have h (j : ℤ) : δ * (x / δ - (j : ℝ)) = x - δ * (j : ℝ) := by
      field_simp
    simpa only [h, Real.dist_eq] using H

lemma triangularFold_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    triangularFold δ x ≤ δ / 2 := by
  rw [triangularFold_eq_round hδ]
  have H := mul_le_mul_of_nonneg_left (abs_sub_round (x / δ)) hδ.le
  have h : x - δ * (round (x / δ) : ℝ) =
      δ * (x / δ - (round (x / δ) : ℝ)) := by field_simp
  rw [h, abs_mul, abs_of_pos hδ]
  nlinarith

lemma triangularFold_piecewise {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    ∃ k : ℤ, triangularFold δ x = x - δ * (k : ℝ) ∨
      triangularFold δ x = -(x - δ * (k : ℝ)) := by
  refine ⟨round (x / δ), ?_⟩
  rw [triangularFold_eq_round hδ]
  exact abs_choice _

end WeakHessian

end

end OAI
