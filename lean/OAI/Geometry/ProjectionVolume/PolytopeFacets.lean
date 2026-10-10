import OAI.Geometry.ProjectionVolume.PolytopeFaceGeometry

namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace Paper092.HPolytope

variable {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι)

theorem affineSpan_face_of_essential (i : ι)
    (hessential : ¬ ∀ x : Euclidean d,
      (∀ j, j ≠ i → ⟪P.normal j, x⟫ ≤ P.offset j) → ⟪P.normal i, x⟫ ≤ P.offset i) :
    (affineSpan ℝ (P.face i) : Set (Euclidean d)) =
      {y | ⟪P.normal i, y⟫ = P.offset i} := by
  classical
  let Q : AffineSubspace ℝ (Euclidean d) :=
    (affineSpan ℝ ({P.offset i} : Set ℝ)).comap (innerₛₗ ℝ (P.normal i)).toAffineMap
  have hQ (y : Euclidean d) : y ∈ Q ↔ ⟪P.normal i, y⟫ = P.offset i := by
    simp [Q]
  have hle : affineSpan ℝ (P.face i) ≤ Q := by
    apply affineSpan_le.mpr
    intro y hy
    exact (hQ y).mpr hy.2
  ext y
  constructor
  · exact fun hy => (hQ y).mp (hle hy)
  · intro hy
    change ⟪P.normal i, y⟫ = P.offset i at hy
    change y ∈ affineSpan ℝ (P.face i)
    obtain ⟨x, hx, hxstrict⟩ := P.exists_strict_face_point_of_essential i hessential
    have hxspan : x ∈ affineSpan ℝ (P.face i) := subset_affineSpan ℝ _ hx
    by_cases hxy : y = x
    · simpa only [hxy] using hxspan
    let S : Set (Euclidean d) := ⋂ j : {j : ι // j ≠ i},
      {z | ⟪P.normal j.val, z⟫ < P.offset j.val}
    have hopen : IsOpen S := isOpen_iInter_of_finite fun j =>
      isOpen_lt (innerSL ℝ (P.normal j.val)).continuous continuous_const
    have hxS : x ∈ S := mem_iInter.mpr (fun j => hxstrict j.val j.property)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hxS
    have hnorm : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    let t : ℝ := ε / (2 * ‖y - x‖)
    have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hnorm)
    let z := x + t • (y - x)
    have hzball : z ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      change ‖x + t • (y - x) - x‖ < ε
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      dsimp [t]
      have heq : ε / (2 * ‖y - x‖) * ‖y - x‖ = ε / 2 := by field_simp
      rw [heq]
      linarith
    have hzS := hball hzball
    have hzi : ⟪P.normal i, z⟫ = P.offset i := by
      dsimp [z]
      simp only [inner_add_right, real_inner_smul_right, inner_sub_right, hy, hx.2,
        sub_self, mul_zero, add_zero]
    have hzface : z ∈ P.face i := by
      refine ⟨?_, hzi⟩
      intro j
      by_cases hji : j = i
      · simpa only [hji, hzi] using le_refl (P.offset i)
      · exact (mem_iInter.mp hzS ⟨j, hji⟩).le
    have hzspan := subset_affineSpan ℝ (P.face i) hzface
    have hmem := (affineSpan ℝ (P.face i)).smul_vsub_vadd_mem t⁻¹ hzspan hxspan hxspan
    have heq : t⁻¹ • (z - x) + x = y := by
      dsimp [z]
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, sub_add_cancel]
    simpa only [vsub_eq_sub, vadd_eq_add, heq] using hmem

end Paper092.HPolytope

end

end OAI
