import OAI.Geometry.ProjectionVolume.PolytopeFront
import OAI.Geometry.ProjectionVolume.ExposedBounds
import Mathlib.Analysis.Convex.Intrinsic

namespace OAI

universe uι

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

namespace Paper092

theorem inner_eq_of_mem_intrinsicInterior {d : ℕ} {S : Set (Euclidean d)}
    {x : Euclidean d} (hx : x ∈ intrinsicInterior ℝ S) (v : Euclidean d)
    (hmax : ∀ z ∈ S, ⟪v, z⟫ ≤ ⟪v, x⟫) :
    ∀ z ∈ S, ⟪v, z⟫ = ⟪v, x⟫ := by
  obtain ⟨xQ, hxQ, rfl⟩ := mem_intrinsicInterior.mp hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxQ)
  intro z hz
  by_cases hzx : z = xQ.val
  · simp only [hzx]
  let t : ℝ := ε / (2 * ‖xQ.val - z‖)
  have hnorm : 0 < ‖xQ.val - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hzx))
  have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hnorm)
  let y : affineSpan ℝ S := ⟨xQ.val + t • (xQ.val - z), by
    simpa only [vsub_eq_sub, vadd_eq_add, add_comm] using
      (affineSpan ℝ S).smul_vsub_vadd_mem t xQ.property
        (subset_affineSpan ℝ S hz) xQ.property⟩
  have hyball : y ∈ Metric.ball xQ ε := by
    change dist (xQ.val + t • (xQ.val - z)) xQ.val < ε
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have heq : t * ‖xQ.val - z‖ = ε / 2 := by
      dsimp [t]
      field_simp
    rw [heq]
    linarith
  have hy : y.val ∈ S := hball hyball
  have hle := hmax y.val hy
  change ⟪v, xQ.val + t • (xQ.val - z)⟫ ≤ ⟪v, xQ.val⟫ at hle
  rw [inner_add_right, real_inner_smul_right, inner_sub_right] at hle
  exact le_antisymm (hmax z hz) (by nlinarith)

namespace HPolytope

variable {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι)

theorem exists_active_of_mem_exposedFace {u x : Euclidean d} (hu : u ≠ 0)
    (hx : x ∈ exposedFace P.body u) : ∃ i, x ∈ P.face i := by
  obtain ⟨t, ht, hxt, i, _, hi⟩ := P.exists_front_point x u hu hx.1
  have hmax := hx.2 (x + t • u) hxt
  change ⟪u, x + t • u⟫ ≤ ⟪u, x⟫ at hmax
  rw [inner_add_right, real_inner_smul_right] at hmax
  have hpos := real_inner_self_pos.mpr hu
  have ht0 : t = 0 := by nlinarith
  refine ⟨i, hx.1, ?_⟩
  change P.offset i - ⟪P.normal i, x + t • u⟫ = 0 at hi
  simp only [ht0, zero_smul, add_zero] at hi
  exact (sub_eq_zero.mp hi).symm

theorem exposedFace_eq_face {u : Euclidean d} (hu : u ≠ 0)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (exposedFace P.body u)) = d - 1) :
    ∃ i, exposedFace P.body u = P.face i := by
  have hconv : Convex ℝ (exposedFace P.body u) :=
    (show IsExposed ℝ P.body (exposedFace P.body u) from
      ContinuousLinearMap.toExposed.isExposed).convex P.body_convex
  have hne := exposedFace_nonempty P.body P.compact P.body_nonempty u
  obtain ⟨x, hx⟩ := (intrinsicInterior_nonempty hconv).mpr hne
  have hxF : x ∈ exposedFace P.body u := intrinsicInterior_subset hx
  obtain ⟨i, hxi⟩ := P.exists_active_of_mem_exposedFace hu hxF
  have hinner : ∀ z ∈ exposedFace P.body u, ⟪P.normal i, z⟫ = P.offset i := by
    intro z hz
    apply Eq.trans (inner_eq_of_mem_intrinsicInterior hx (P.normal i) ?_ z hz) hxi.2
    intro y hy
    rw [hxi.2]
    exact hy.1 i
  have hle : vectorSpan ℝ (exposedFace P.body u) ≤ normalHyperplane (P.normal i) := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, b, hb, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    change ⟪P.normal i, a - b⟫ = 0
    rw [inner_sub_right, hinner a ha, hinner b hb, sub_self]
  have hn : P.normal i ≠ 0 := by
    intro h
    have hnorm := P.normal_unit i
    rw [h, norm_zero] at hnorm
    norm_num at hnorm
  have hspan_i : vectorSpan ℝ (exposedFace P.body u) = normalHyperplane (P.normal i) :=
    Submodule.eq_of_le_of_finrank_eq hle (hdim.trans (normalHyperplane_finrank _ hn).symm)
  have hspan_u : vectorSpan ℝ (exposedFace P.body u) = normalHyperplane u :=
    Submodule.eq_of_le_of_finrank_eq (exposedFace_vectorSpan_le_normalHyperplane P.body u)
      (hdim.trans (normalHyperplane_finrank u hu).symm)
  refine ⟨i, Subset.antisymm (fun z hz => ⟨hz.1, hinner z hz⟩) ?_⟩
  intro y hy
  have hyi : y - x ∈ normalHyperplane (P.normal i) := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [inner_sub_right, hy.2, hxi.2, sub_self]
  have hyu : y - x ∈ normalHyperplane u := by
    rwa [← hspan_u, hspan_i]
  have heq : ⟪u, y⟫ = ⟪u, x⟫ := by
    have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hyu
    simpa only [inner_sub_right, sub_eq_zero] using h
  refine ⟨hy.1, ?_⟩
  intro z hz
  change ⟪u, z⟫ ≤ ⟪u, y⟫
  rw [heq]
  exact hxF.2 z hz

end HPolytope
end Paper092

end

end OAI
