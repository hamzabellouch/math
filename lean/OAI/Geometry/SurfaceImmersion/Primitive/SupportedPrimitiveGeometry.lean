import OAI.Geometry.SurfaceImmersion.Atlas.AtlasImmersionGeometry
import OAI.Geometry.SurfaceImmersion.Atlas.UniformMetricPhaseGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveNormal

namespace OAI

/-! The local primitive normal bound and exterior C2 proximity together
preserve immersion and a nonzero second form on the entire surface. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_eventuallyEq_at {F G : M → Space} {p : M}
    (hFG : F =ᶠ[𝓝 p] G) (q : M) (hp : p ∈ (coordinateChart q).source) :
    coordinateMap F q =ᶠ[𝓝 (coordinateChart q p)] coordinateMap G q := by
  have ht : Tendsto (coordinateChart q).symm (𝓝 (coordinateChart q p)) (𝓝 p) := by
    simpa only [(coordinateChart q).left_inv hp] using
      ((coordinateChart q).continuousAt_symm ((coordinateChart q).map_source hp)).tendsto
  filter_upwards [hFG.comp_tendsto ht] with x hx
  change spaceCoordinates (F (coordinateInverse q x)) = spaceCoordinates (G (coordinateInverse q x))
  rw [← coordinateChart_symm_apply]
  exact congrArg spaceCoordinates hx

namespace FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation JetVelocityCoordinates SurfaceJetCoordinates SurfaceVelocityFamily.Loop
variable [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma planeRead_eventuallyEq_on_weight {F G : M → Space} {p : M}
    (hFG : F =ᶠ[𝓝 p] G) (i : A.centers) (hp : p ∈ tsupport (A.weight i))
    (houter : ∀ x ∈ tsupport (A.weight i), A.outer i =ᶠ[𝓝 x] (fun _ => 1)) :
    (spaceCoordinates ∘ A.vectorPlaneRead i F) =ᶠ[
      𝓝 (planeCoordinateIsometry (chart (i : M) p))]
        (spaceCoordinates ∘ A.vectorPlaneRead i G) := by
  have he := coordinateMap_eventuallyEq_at hFG (i : M)
    (by simpa [coordinateChart_source,chart] using A.weight_support i hp)
  have hpoint : coordinateChart (i : M) p = planeCoordinateIsometry (chart (i : M) p) := by
    rw [planeCoordinateIsometry_chart]
    rfl
  rw [hpoint] at he
  exact (A.vectorPlaneRead_eventually_coordinateMap F i houter hp).trans
    (he.trans (A.vectorPlaneRead_eventually_coordinateMap G i houter hp).symm)

end SmoothingAtlas
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

theorem supported_primitive_geometry (data : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) (i : data.A.centers) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (G V : M → Space), ContMDiff planeModel spaceModel ∞ G →
        ContMDiff planeModel spaceModel ∞ V → ∀ b : ℝ, 0 ≤ b → b < ρ →
      data.A.WeightedBound 1 2 b (G-F) →
      (∀ p ∈ tsupport (data.A.weight i),
        let H := primitiveNormalTriple (data.A.vectorChartRead i V) (chart (i : M) p)
        NormalFrame.gramDet (H 0) (H 1) ≠ 0 ∧ realNormalPart (H 0) (H 1) (H 2) ≠ 0) →
      (∀ p ∉ tsupport (data.A.weight i), V =ᶠ[𝓝 p] G) →
      (∀ p, Function.Injective (mfderiv planeModel spaceModel V p)) ∧
      (∀ p, ∃ v w : SmallModes.Base,
        realSecondForm (coordinateMap V p) v w (coordinateCenter p) ≠ 0) := by
  obtain ⟨ρ,hρ,hnear⟩ := data.uniform_C2_geometry hF
  refine ⟨ρ,hρ,?_⟩
  intro G V hG hV b hb hbρ hclose hnormal hexterior
  obtain ⟨hImm,hgood,_⟩ := hnear G hG b hb hbρ hclose
  apply data.A.geometry_of_chartwise_good hV data.outer_locally_one
  intro p
  by_cases hp : p ∈ tsupport (data.A.weight i)
  · obtain ⟨hD,hN⟩ := hnormal p hp
    have hh := good_phase_of_primitive_normal
      (spaceCoordinates.contDiff.comp (data.A.vectorPlaneRead_smooth i hV))
      (chart (i : M) p)
      (by rw [data.A.vectorChartRead_from_plane]; exact hD)
      (by rw [data.A.vectorChartRead_from_plane]; exact hN)
    exact ⟨i,hp,hh.1,dx,hh.2⟩
  · obtain ⟨j,hj⟩ : ∃ j : data.A.centers, data.A.weight j p ≠ 0 := by
      by_contra! hzero
      have hh := data.A.partition p
      simp only [hzero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at hh
      norm_num at hh
    have hjp : p ∈ tsupport (data.A.weight j) := subset_tsupport _ hj
    have hx : planeCoordinateIsometry (chart (j : M) p) ∈
        (modeSupport (data.A.chartWeightCompact j) : Set SmallModes.Base) :=
      ⟨chart (j : M) p,⟨p,hjp,rfl⟩,rfl⟩
    have he := data.A.planeRead_eventuallyEq_on_weight (hexterior p hp) j hjp
      (data.outer_locally_one j)
    refine ⟨j,hjp,?_,(data.Q j).ξ 0,?_⟩
    · rw [he.fderiv_eq]
      exact hImm j _ hx
    · rw [(realSecondTensor_eventuallyEq he).eq_of_nhds]
      exact hgood j 0 _ hx

end MetricGoodPhaseData
end FiniteOrderSmoothing
end ClosedSurfaceR4

end

end OAI
