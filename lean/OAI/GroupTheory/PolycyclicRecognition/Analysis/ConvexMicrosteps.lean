import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OAI

/-! # Convex control of the actual microstep sum

The unfinished final microstep is filled with one fixed label. Its cost is
explicit, so the number of full steps need not divide the total time.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped BigOperators
open Metric Set

/-- The convex error of a weighted sum is bounded by the sum of its label
errors and the exact remainder error. The labels are chosen only in a finite
sum; no measurable choice is used. -/
theorem infDist_weighted_sum_le
    {ι W : Type*} [Fintype ι] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {S : Set W} (hS : IsCompact S) {w₀ : W} (hw₀ : w₀ ∈ S)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i ≤ 1)
    (x : ι → W) (e : W) :
    infDist ((∑ i, a i • x i) + e) (convexHull ℝ S) ≤
      (∑ i, a i * infDist (x i) S) + ‖e - (1 - ∑ i, a i) • w₀‖ := by
  choose y hy hdist using fun i => hS.exists_infDist_eq_dist ⟨w₀, hw₀⟩ (x i)
  let b : Option ι → ℝ := fun i => i.elim (1 - ∑ i, a i) a
  let z : Option ι → W := fun i => i.elim w₀ y
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    cases i with
    | none => exact sub_nonneg.mpr hsum
    | some i => exact ha i
  have hb1 : ∑ i, b i = 1 := by simp [b, Fintype.sum_option]
  have hz : ∀ i, z i ∈ convexHull ℝ S := by
    intro i
    apply subset_convexHull
    cases i with
    | none => exact hw₀
    | some i => exact hy i
  have hmem := (convex_convexHull ℝ S).sum_mem
    (t := Finset.univ) (w := b) (z := z) (fun i _ => hb i) hb1 (fun i _ => hz i)
  have hmem' : (∑ i, a i • y i) + (1 - ∑ i, a i) • w₀ ∈ convexHull ℝ S := by
    simpa only [b, z, Fintype.sum_option, Option.elim_none, Option.elim_some, add_comm] using hmem
  calc
    _ ≤ dist ((∑ i, a i • x i) + e)
        ((∑ i, a i • y i) + (1 - ∑ i, a i) • w₀) := infDist_le_dist_of_mem hmem'
    _ = ‖(∑ i, a i • (x i - y i)) + (e - (1 - ∑ i, a i) • w₀)‖ := by
      rw [dist_eq_norm]
      congr 1
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    _ ≤ ‖∑ i, a i • (x i - y i)‖ + ‖e - (1 - ∑ i, a i) • w₀‖ := norm_add_le _ _
    _ ≤ (∑ i, ‖a i • (x i - y i)‖) + ‖e - (1 - ∑ i, a i) • w₀‖ :=
      add_le_add (norm_sum_le _ _) le_rfl
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha i), hdist i, dist_eq_norm]

end PolycyclicRecognition

end

end OAI
