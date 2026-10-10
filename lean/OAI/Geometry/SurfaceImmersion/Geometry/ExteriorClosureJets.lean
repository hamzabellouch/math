import OAI.Geometry.SurfaceImmersion.Geometry.ExteriorApproximation

namespace OAI

/-! Smooth comparison maps agreeing on an open exterior have equal jets
at its boundary. This retains the disk boundary in exterior C2 estimates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma planeRead_eventuallyEq_at_source {F G : M → Space} {p : M}
    (hFG : F =ᶠ[𝓝 p] G) (i : A.centers) (hp : p ∈ (chart (i : M)).source) :
    (spaceCoordinates ∘ A.vectorPlaneRead i F) =ᶠ[
      𝓝 (planeCoordinateIsometry (chart (i : M) p))]
        (spaceCoordinates ∘ A.vectorPlaneRead i G) := by
  have ht : Tendsto (fun x : SmallModes.Base => (chart (i : M)).symm (planeCoordinateIsometry.symm x))
      (𝓝 (planeCoordinateIsometry (chart (i : M) p))) (𝓝 p) := by
    have hc : Tendsto (chart (i : M)).symm (𝓝 (chart (i : M) p)) (𝓝 p) := by
      simpa only [(chart (i : M)).left_inv hp] using
        ((chart (i : M)).continuousAt_symm ((chart (i : M)).map_source hp)).tendsto
    have hi : Tendsto planeCoordinateIsometry.symm
        (𝓝 (planeCoordinateIsometry (chart (i : M) p))) (𝓝 (chart (i : M) p)) := by
      simpa only [LinearIsometryEquiv.symm_apply_apply] using
        (planeCoordinateIsometry.symm.continuousAt (x := planeCoordinateIsometry (chart (i : M) p))).tendsto
    exact hc.comp hi
  filter_upwards [hFG.comp_tendsto ht] with x hx
  change spaceCoordinates (localize (i : M) (A.outer i) F (planeCoordinateIsometry.symm x)) =
    spaceCoordinates (localize (i : M) (A.outer i) G (planeCoordinateIsometry.symm x))
  unfold localize
  by_cases hxT : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target
  · simp only [indicator_of_mem hxT]
    change F ((chart (i : M)).symm (planeCoordinateIsometry.symm x)) =
      G ((chart (i : M)).symm (planeCoordinateIsometry.symm x)) at hx
    rw [hx]
  · simp only [indicator_of_notMem hxT]

lemma planeRead_jets_eq_on_exterior_closure {F G : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hG : ContMDiff planeModel spaceModel ∞ G)
    {O : Set M} (hext : ∀ p ∈ O, F =ᶠ[𝓝 p] G)
    (i : A.centers) (m : ℕ) :
    ∀ p ∈ closure O, p ∈ (chart (i : M)).source →
      iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)) =
      iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead i G)
        (planeCoordinateIsometry (chart (i : M) p)) := by
  let U := (chart (i : M)).source
  have hU : IsOpen U := (chart (i : M)).open_source
  let a := fun p => iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead i F)
    (planeCoordinateIsometry (chart (i : M) p))
  let b := fun p => iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead i G)
    (planeCoordinateIsometry (chart (i : M) p))
  have hca : ContinuousOn a U :=
    ((spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)).continuous_iteratedFDeriv
      (by simp)).comp_continuousOn (planeCoordinateIsometry.continuous.comp_continuousOn (chart (i : M)).continuousOn)
  have hcb : ContinuousOn b U :=
    ((spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)).continuous_iteratedFDeriv
      (by simp)).comp_continuousOn (planeCoordinateIsometry.continuous.comp_continuousOn (chart (i : M)).continuousOn)
  have he : EqOn a b (O ∩ U) := by
    intro p hp
    exact ((A.planeRead_eventuallyEq_at_source (hext p hp.1) i hp.2).iteratedFDeriv ℝ m).eq_of_nhds
  have hclosed := he.of_subset_closure (hca.mono inter_subset_right) (hcb.mono inter_subset_right)
    (fun p hp => ⟨subset_closure hp.1,hp.2⟩) hU.closure_inter
  exact fun p hp hpU => hclosed ⟨hp,hpU⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
