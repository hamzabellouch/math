import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.AffinePlaneNormalFrame

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem exists_affine_n_plane {n d : ℕ} (hnd : n ≤ d) :
    ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S := by
  obtain ⟨L⟩ := exists_euclidean_isometric_embedding hnd
  refine ⟨L.toLinearMap.range.toAffineSubspace, ⟨0, ?_⟩, ?_⟩
  · exact L.toLinearMap.range.zero_mem
  · rw [Submodule.toAffineSubspace_direction, LinearMap.finrank_range_of_inj L.injective]
    exact finrank_euclideanSpace_fin

theorem exists_approximate_plane_fit {n d : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (a : Ambient d) (r ε : ℝ) (hε : 0 < ε) :
    ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
      quadraticPlaneError n μ a r S < squaredExcess n μ a r + ε := by
  obtain ⟨S, hS⟩ := exists_affine_n_plane hnd
  have hne : {t : ℝ | ∃ T : AffineSubspace ℝ (Ambient d),
      IsAffineNPlane n T ∧ t = quadraticPlaneError n μ a r T}.Nonempty :=
    ⟨quadraticPlaneError n μ a r S, S, hS, rfl⟩
  obtain ⟨t, ⟨T, hT, ht⟩, hlt⟩ := exists_lt_of_csInf_lt hne
    (show squaredExcess n μ a r < squaredExcess n μ a r + ε from lt_add_of_pos_right _ hε)
  exact ⟨T, hT, ht ▸ hlt⟩

theorem quadraticPlaneError_integral_identity {n d : ℕ}
    (μ : Measure (Ambient d)) (a : Ambient d) (r : ℝ) (hr : r ≠ 0)
    (S : AffineSubspace ℝ (Ambient d)) :
    r ^ (n + 2) * quadraticPlaneError n μ a r S =
      ∫ x in ball a r, infDist x (S : Set (Ambient d)) ^ 2 ∂μ := by
  rw [quadraticPlaneError, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr), one_mul]

theorem eventually_excess_below_scale {n d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (a : Ambient d) (r : ℝ)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j)
    (hlim : Tendsto (fun j => squaredExcess n (μ j) a r / δ j ^ 2) atTop (𝓝 0))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ j in atTop, squaredExcess n (μ j) a r < η * δ j ^ 2 := by
  filter_upwards [hlim.eventually (gt_mem_nhds hη)] with j hj
  exact (div_lt_iff₀ (sq_pos_of_pos (hδ j))).mp hj

end

end RieszRectifiability

end OAI
