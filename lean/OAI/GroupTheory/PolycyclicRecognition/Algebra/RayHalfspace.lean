import OAI.GroupTheory.PolycyclicRecognition.Geometry.PositiveWeightCones
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology

namespace OAI

/-!
# Outside-ray weights on a negative halfspace

This is the linear-algebraic construction in the representative-independence
part of `boundary.tex`: a nonzero form outside a positive ray is unbounded
above on every fixed negative halfspace for that ray.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A nonzero form outside the positive `α` ray is unbounded above while
the `α` height stays below the height of a fixed negative point. -/
theorem exists_large_weight_in_negative_halfspace
    (α β : V →ₗ[ℝ] ℝ) (v₀ : V) (hα : α v₀ < 0)
    (hβ : β ≠ 0) (hout : β ∉ positiveWeightRay α) (R : ℝ) :
    ∃ v : V, α v ≤ α v₀ ∧ R ≤ β v := by
  classical
  by_cases hker : ∃ z : V, α z = 0 ∧ β z ≠ 0
  · obtain ⟨z, hzα, hzβ⟩ := hker
    let w := (β z)⁻¹ • z
    have hwα : α w = 0 := by simp [w, hzα]
    have hwβ : β w = 1 := by simp [w, hzβ]
    refine ⟨v₀ + (R - β v₀) • w, ?_, ?_⟩
    · simp [hwα]
    · simp only [map_add, map_smul, smul_eq_mul, hwβ, mul_one]
      linarith
  · have hker' (z : V) (hz : α z = 0) : β z = 0 := by
      by_contra hn
      exact hker ⟨z, hz, hn⟩
    have hα0 : α v₀ ≠ 0 := ne_of_lt hα
    have he (v : V) : β v = (β v₀ / α v₀) * α v := by
      have hz : α (v - (α v / α v₀) • v₀) = 0 := by
        simp only [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hα0, sub_self]
      have hb := hker' _ hz
      simp only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hb
      rw [hb]
      ring
    have hβ0 : β v₀ ≠ 0 := by
      intro hz
      apply hβ
      apply LinearMap.ext
      intro v
      simpa only [hz, zero_div, zero_mul, LinearMap.zero_apply] using he v
    have hβpos : 0 < β v₀ := by
      by_contra hn
      have hβneg : β v₀ < 0 := lt_of_le_of_ne (le_of_not_gt hn) hβ0
      apply hout
      refine ⟨β v₀ / α v₀, div_pos_of_neg_of_neg hβneg hα, ?_⟩
      apply LinearMap.ext
      intro v
      simpa only [LinearMap.smul_apply, smul_eq_mul] using he v
    let t := max 1 (R / β v₀)
    refine ⟨t • v₀, ?_, ?_⟩
    · simp only [map_smul, smul_eq_mul]
      calc
        t * α v₀ ≤ 1 * α v₀ := mul_le_mul_of_nonpos_right (le_max_left _ _) hα.le
        _ = α v₀ := one_mul _
    · simp only [map_smul, smul_eq_mul]
      exact (div_le_iff₀ hβpos).mp (le_max_right _ _)

/-- Finitely many outside-ray forms can simultaneously have arbitrarily
large support on one compact convex set in the fixed negative halfspace. -/
theorem exists_compact_negative_halfspace_template
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {I : Type*} [Fintype I]
    (α : V →ₗ[ℝ] ℝ) (β : I → V →ₗ[ℝ] ℝ)
    (v₀ : V) (hα : α v₀ < 0) (hβ : ∀ i, β i ≠ 0) (R : ℝ) :
    ∃ E : Set V, IsCompact E ∧ Convex ℝ E ∧ v₀ ∈ E ∧
      (∀ v ∈ E, α v ≤ α v₀) ∧
      ∀ i, β i ∉ positiveWeightRay α → ∃ v ∈ E, R ≤ β i v := by
  classical
  have hpoint (i : I) : ∃ v : V, α v ≤ α v₀ ∧
      (β i ∉ positiveWeightRay α → R ≤ β i v) := by
    by_cases hi : β i ∈ positiveWeightRay α
    · exact ⟨v₀, le_rfl, fun h => (h hi).elim⟩
    · obtain ⟨v, hv, hR⟩ := exists_large_weight_in_negative_halfspace α (β i) v₀ hα (hβ i) hi R
      exact ⟨v, hv, fun _ => hR⟩
  choose v hv hR using hpoint
  let S := insert v₀ (range v)
  let E := convexHull ℝ S
  have hS : S.Finite := (finite_range v).insert v₀
  refine ⟨E, hS.isCompact_convexHull ℝ, convex_convexHull ℝ S,
    subset_convexHull ℝ S (mem_insert v₀ _), ?_, ?_⟩
  · have hs : S ⊆ {v | α v ≤ α v₀} := by
      intro x hx
      rcases mem_insert_iff.mp hx with rfl | ⟨i, rfl⟩
      · change α x ≤ α x
        exact le_rfl
      · exact hv i
    exact convexHull_min hs (convex_halfSpace_le α.isLinear _)
  · intro i hi
    exact ⟨v i, subset_convexHull ℝ S (mem_insert_of_mem _ (mem_range_self i)), hR i hi⟩

end PolycyclicRecognition

end

end OAI
