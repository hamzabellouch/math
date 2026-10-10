import OAI.Geometry.ProjectionVolume.ExposedProduct

namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace Paper092

theorem exposedFace_vectorSpan_le_normalHyperplane {n : ℕ}
    (K : Set (Euclidean n)) (u : Euclidean n) :
    vectorSpan ℝ (exposedFace K u) ≤ normalHyperplane u := by
  rw [vectorSpan_def]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, y, hy, rfl⟩
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  change ⟪u, x - y⟫ = 0
  rw [inner_sub_right]
  exact sub_eq_zero.mpr (le_antisymm (hy.2 x hx.1) (hx.2 y hy.1))

theorem exposedFace_finrank_le {n : ℕ} (K : Set (Euclidean n))
    {u : Euclidean n} (hu : u ≠ 0) :
    Module.finrank ℝ (vectorSpan ℝ (exposedFace K u)) ≤ n - 1 := by
  have h := Submodule.finrank_mono (exposedFace_vectorSpan_le_normalHyperplane K u)
  rwa [normalHyperplane_finrank u hu] at h

theorem exposedFace_ssubset {n : ℕ} (K : Set (Euclidean n))
    (hint : (interior K).Nonempty) {u : Euclidean n} (hu : u ≠ 0) :
    exposedFace K u ⊂ K := by
  refine ssubset_iff_subset_ne.mpr ⟨fun _ hx => hx.1, ?_⟩
  intro heq
  obtain ⟨x, hx⟩ := hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let t : ℝ := ε / (2 * ‖u‖)
  have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hnorm)
  have hdist : dist (x + t • u) x < ε := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    field_simp
    linarith
  have hy := hball (Metric.mem_ball.mpr hdist)
  have hface : x ∈ exposedFace K u := heq.symm ▸ interior_subset hx
  have hle := hface.2 (x + t • u) hy
  change ⟪u, x + t • u⟫ ≤ ⟪u, x⟫ at hle
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at hle
  have hpos := mul_pos ht (sq_pos_of_pos hnorm)
  linarith

end Paper092

end

end OAI
