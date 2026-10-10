import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PositiveWeightCones

namespace OAI

/-! # Uniform separation after deleting a whole positive weight ray

The original generator list may contain repeated positive rays. A positive
balanced relation still makes the remaining rays separate the height space.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [Fintype I]

/-- A balanced positive family cannot be positive on its only nonzero ray. -/
theorem nonpos_of_vanishing_outside_positive_ray
    (α : I → W →ₗ[ℝ] ℝ) (c : I → ℝ) (hc : ∀ i, 0 < c i)
    (hrel : ∀ w, ∑ i, c i * α i w = 0)
    (k : I) (w : W)
    (hw : ∀ i, α i ∉ positiveWeightRay (α k) → α i w = 0) : α k w ≤ 0 := by
  by_contra h
  have hk : 0 < α k w := lt_of_not_ge h
  have hnonneg (i : I) : 0 ≤ c i * α i w := by
    by_cases hi : α i ∈ positiveWeightRay (α k)
    · obtain ⟨t, ht, he⟩ := hi
      rw [he, LinearMap.smul_apply, smul_eq_mul]
      exact (mul_pos (hc i) (mul_pos ht hk)).le
    · rw [hw i hi, mul_zero]
  have hsum : 0 < ∑ i, c i * α i w := Finset.sum_pos'
    (fun i _ => hnonneg i) ⟨k, Finset.mem_univ k, mul_pos (hc k) hk⟩
  rw [hrel] at hsum
  exact lt_irrefl _ hsum

/-- Removing every duplicate of one positive ray preserves separation. -/
theorem separates_outside_positive_ray
    (α : I → W →ₗ[ℝ] ℝ) (c : I → ℝ) (hc : ∀ i, 0 < c i)
    (hrel : ∀ w, ∑ i, c i * α i w = 0)
    (hsep : ∀ w, (∀ i, α i w = 0) → w = 0)
    (k : I) (w : W)
    (hw : ∀ i, α i ∉ positiveWeightRay (α k) → α i w = 0) : w = 0 := by
  have hk : α k w = 0 := by
    have hp := nonpos_of_vanishing_outside_positive_ray α c hc hrel k w hw
    have hn := nonpos_of_vanishing_outside_positive_ray α c hc hrel k (-w)
      (fun i hi => by simp only [map_neg, hw i hi, neg_zero])
    rw [map_neg] at hn
    linarith
  apply hsep w
  intro i
  by_cases hi : α i ∈ positiveWeightRay (α k)
  · obtain ⟨t, _, he⟩ := hi
    simp only [he, LinearMap.smul_apply, smul_eq_mul, hk, mul_zero]
  · exact hw i hi

/-- The norm bound is uniform over the finite generator list, including
when several generators determine the same positive ray. -/
theorem exists_bound_outside_positive_ray [FiniteDimensional ℝ W]
    (α : I → W →ₗ[ℝ] ℝ) (c : I → ℝ) (hc : ∀ i, 0 < c i)
    (hrel : ∀ w, ∑ i, c i * α i w = 0)
    (hsep : ∀ w, (∀ i, α i w = 0) → w = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : I) (w : W) (B : ℝ), 0 ≤ B →
      (∀ i, α i ∉ positiveWeightRay (α k) → |α i w| ≤ B) → ‖w‖ ≤ C * B := by
  classical
  have hlocal (k : I) : ∃ C : ℝ, 0 < C ∧ ∀ (w : W) (B : ℝ), 0 ≤ B →
      (∀ i, α i ∉ positiveWeightRay (α k) → |α i w| ≤ B) → ‖w‖ ≤ C * B := by
    obtain ⟨C, hC, hb⟩ := exists_bound_of_separating_forms
      (fun i : {i : I // α i ∉ positiveWeightRay (α k)} => α i)
      (fun w hw => separates_outside_positive_ray α c hc hrel hsep k w
        (fun i hi => hw ⟨i, hi⟩))
    exact ⟨C, hC, fun w B hB hw => hb w B hB (fun i => hw i i.property)⟩
  choose C hC hbound using hlocal
  have hs : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => (hC i).le)
  refine ⟨(∑ i, C i) + 1, by linarith, ?_⟩
  intro k w B hB hw
  apply (hbound k w B hB hw).trans
  apply mul_le_mul_of_nonneg_right _ hB
  have hk : C k ≤ ∑ i, C i := Finset.single_le_sum
    (fun i _ => (hC i).le) (Finset.mem_univ k)
  linarith

end PolycyclicRecognition

end

end OAI
