import OAI.Geometry.SurfaceImmersion.Geometry.SplitSardCompact
import Mathlib.Analysis.Normed.Ring.Units

namespace OAI

/-! Finite-dimensional critical loci are closed. This supplies compact
exhaustions for the fiberwise critical-value argument. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem surjective_clm_open : IsOpen {K : E →L[ℝ] F | Function.Surjective K} := by
  rw [isOpen_iff_mem_nhds]
  intro K hK
  obtain ⟨R,hR⟩ := K.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hK)
  let R' : F →L[ℝ] E := R.toContinuousLinearMap
  have hKR : K.comp R' = ContinuousLinearMap.id ℝ F := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun L : F →ₗ[ℝ] F => L x) hR
  have hc : Continuous (fun L : E →L[ℝ] F => L.comp R') := continuous_id.clm_comp continuous_const
  have hn : ∀ᶠ L in 𝓝 K, IsUnit (L.comp R') := by
    change (fun L : E →L[ℝ] F => L.comp R') ⁻¹' {A | IsUnit A} ∈ 𝓝 K
    apply hc.continuousAt.preimage_mem_nhds
    apply Units.isOpen.mem_nhds
    rw [hKR]
    exact isUnit_one
  filter_upwards [hn] with L hL
  obtain ⟨u,hu⟩ := hL
  intro y
  refine ⟨R' ((↑u⁻¹ : F →L[ℝ] F) y),?_⟩
  have hval : L (R' ((↑u⁻¹ : F →L[ℝ] F) y)) =
      (↑u : F →L[ℝ] F) ((↑u⁻¹ : F →L[ℝ] F) y) := by rw [hu]; rfl
  rw [hval]
  change ((u : F →L[ℝ] F) * (↑u⁻¹ : F →L[ℝ] F)) y = y
  simp

theorem smooth_critical_set_closed {f : E → F} (hf : ContDiff ℝ ∞ f) :
    IsClosed {x | ¬ Function.Surjective (fderiv ℝ f x)} :=
  (surjective_clm_open.preimage (hf.continuous_fderiv (by simp))).isClosed_compl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
