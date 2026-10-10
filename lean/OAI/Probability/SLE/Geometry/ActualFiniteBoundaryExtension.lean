import OAI.Probability.SLE.Loewner.InverseBoundaryShrink
import OAI.Probability.SLE.Geometry.HalfPlaneBoundaryExtension
import OAI.Probability.SLE.Geometry.PublishedFiniteBoundaryExtension

namespace OAI

/-! The finite boundary extension required by the SLE application,
proved from the capacity witness. Small inverse half-disks are Cauchy;
completeness gives the boundary limits and the existing tip limit fixes
the extension at the driver. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology NNReal

namespace SLEExactGauge

lemma IsCapacityTwoWitness.finite_real_boundary_limit
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (x : ℝ) :
    ∃ z : ℂ, Tendsto (F t) (𝓝[upperHalfPlane] (x:ℂ)) (𝓝 z) := by
  have hx : (x:ℂ)∈closure upperHalfPlane :=
    closedHalfPlane_subset_closure_upperHalfPlane (by simp)
  have : NeBot (𝓝[upperHalfPlane] (x:ℂ)) := mem_closure_iff_nhdsWithin_neBot.mp hx
  apply cauchy_map_iff_exists_tendsto.mp
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance,fun ε hε => ?_⟩
  obtain ⟨r,hr,z,hsmall⟩ := hw.small_boundary_halfdisk t x (ε/3) (by positivity)
  refine ⟨F t '' (upperHalfPlane∩ball (x:ℂ) r),?_,?_⟩
  · change (F t) ⁻¹' (F t '' (upperHalfPlane∩ball (x:ℂ) r))∈𝓝[upperHalfPlane] (x:ℂ)
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (x:ℂ) hr)] with w hwH hwr
    exact ⟨w,⟨hwH,hwr⟩,rfl⟩
  · rintro a ⟨u,hu,rfl⟩ b ⟨v,hv,rfl⟩
    have hsu := hsmall u hu.1 hu.2
    have hsv := hsmall v hv.1 hv.2
    have htri := dist_triangle (F t u) z (F t v)
    rw [dist_comm z (F t v)] at htri
    linarith

/-- Continuous finite boundary extension of the inverse Loewner map. -/
theorem actual_finiteLoewnerBoundaryExtension : PublishedFiniteLoewnerBoundaryExtension := by
  intro U γ G F _hU hw t
  exact hw.boundary_extension_of_real_limits t (hw.finite_real_boundary_limit t)

end SLEExactGauge

end

end OAI
