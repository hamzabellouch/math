import OAI.Geometry.SurfaceImmersion.Atlas.ShrinkingWeightContinuity

namespace OAI

/-! A fixed smooth multiplier for a whole compact range of smaller radii.
This removes the apparent moving denominator from all derivative estimates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

/-- The ratio-cutoff family is multiplication by one fixed smooth function
on every smaller radius box. Constants for that multiplier are chosen before
any radius in the box. -/
theorem exists_shrinkingWeight_multiplier (p : M) (w : M → ℝ)
    (hw : ContMDiff planeModel 𝓘(ℝ) ∞ w) {r0 R : ℝ}
    (hreg0 : circularCoordinateRegion p r0 ⊆ (coordinateChart p).target)
    (hR : R^2 < r0^2) :
    ∃ a : M → ℝ, ContMDiff planeModel 𝓘(ℝ) ∞ a ∧
      tsupport a ⊆ circularCoordinateDisk p r0 ∧
      ∀ r : ℝ, r^2 ≤ R^2 → shrinkingCircularWeight p w r0 r =
        fun x => a x * circularManifoldBump p r x := by
  have hreg := (circularCoordinateRegion_mono p hR.le).trans hreg0
  have hK := circularDiskClosure_compact p R hreg
  have hKO := circularDiskClosure_subset_disk p hR hreg
  obtain ⟨B,hB,hKB,hBc⟩ := hK.exists_isOpen_closure_subset
    ((circularCoordinateDisk_open p r0).mem_nhdsSet.mpr hKO)
  obtain ⟨chi,hchi,_,hsupp,hchiK⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (I := planeModel) (n := (⊤ : ℕ∞))
      hB hK.isClosed hKB
  let a : M → ℝ := fun x => chi x * (w x / circularManifoldBump p r0 x)
  have haS : tsupport a ⊆ circularCoordinateDisk p r0 := by
    apply Subset.trans (b := tsupport chi)
    · apply closure_mono
      intro x hx hzero
      exact hx (by simp only [a,hzero,zero_mul])
    · change closure (Function.support chi) ⊆ _
      rw [hsupp]
      exact hBc
  have ha : ContMDiff planeModel 𝓘(ℝ) ∞ a := by
    apply contMDiff_of_tsupport
    intro x hx
    have hp := (circularManifoldBump_pos_iff p x r0).mpr (haS hx)
    exact (hchi x).mul ((hw x).div₀
      ((circularManifoldBump_smooth_support p r0 hreg0).1 x) hp.ne')
  refine ⟨a,ha,haS,?_⟩
  intro r hr
  funext x
  by_cases hz : circularManifoldBump p r x = 0
  · simp only [shrinkingCircularWeight,hz,zero_div,mul_zero]
  · have hreg' := (circularCoordinateRegion_mono p hr).trans hreg
    have hx := (circularManifoldBump_smooth_support p r hreg').2 (subset_tsupport _ hz)
    have hchi1 := (hchiK x).mp (circularDiskClosure_mono p hr hx)
    simp only [a,hchi1,one_mul,shrinkingCircularWeight]
    ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
