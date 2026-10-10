import OAI.Geometry.SurfaceImmersion.Atlas.ShrinkingWeightContinuity
import OAI.Geometry.Immersion.ClosedSurface.AtlasPartition

namespace OAI

/-! One open box of independent radius choices preserves a finite family of
actual circular weights uniformly. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]
variable {ι : Type*} [Fintype ι]

/-- The radius neighborhood is fixed before all independent choices. -/
theorem independent_shrinking_weights (p : ι → M) (w : ι → M → ℝ) (r0 : ι → ℝ)
    (hw : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (w i))
    (hnon : ∀ i x, 0 ≤ w i x) (hr0 : ∀ i, 0 < r0 i)
    (hreg : ∀ i, circularCoordinateRegion (p i) (r0 i) ⊆ (coordinateChart (p i)).target)
    (hpos : ∀ i x, 0 < w i x ↔ x ∈ circularCoordinateDisk (p i) (r0 i))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ (∀ i, delta ≤ r0 i / 2) ∧ ∀ r : ι → ℝ,
      (∀ i, r0 i-delta < r i ∧ r i < r0 i) →
      (∀ i, 0 < r i) ∧
      (∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (shrinkingCircularWeight (p i) (w i) (r0 i) (r i))) ∧
      (∀ i x, 0 < shrinkingCircularWeight (p i) (w i) (r0 i) (r i) x ↔
        x ∈ circularCoordinateDisk (p i) (r i)) ∧
      (∀ i, tsupport (shrinkingCircularWeight (p i) (w i) (r0 i) (r i)) ⊆
        circularDiskClosure (p i) (r i)) ∧
      (∀ i x, |shrinkingCircularWeight (p i) (w i) (r0 i) (r i) x-w i x| < eps) := by
  classical
  choose d hd hdR hnear using fun i => shrinkingCircularWeight_uniform_perturbation
    (p i) (w i) (hw i) (hnon i) (hr0 i) (hreg i) (hpos i) heps
  obtain ⟨delta,hdelta,_,hsmall⟩ := finite_positive_threshold d hd
  refine ⟨delta,hdelta,(fun i => (hsmall i).trans (hdR i)),?_⟩
  intro r hr
  have hri (i : ι) : r0 i-d i < r i := by
    have := hsmall i
    linarith [(hr i).1]
  have hres (i : ι) := hnear i (r i) (hri i) (hr i).2
  refine ⟨?_,fun i => (hres i).1,fun i => (hres i).2.1,
    fun i => (hres i).2.2.1,fun i => (hres i).2.2.2⟩
  intro i
  linarith [hdR i,hr0 i,hri i]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
