import OAI.Geometry.SurfaceImmersion.Primitive.SupportedPrimitiveGeometry
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

namespace FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation JetVelocityCoordinates SurfaceJetCoordinates SurfaceVelocityFamily.Loop
variable [CompactSpace M]
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

theorem supported_patch_geometry (data : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) (i : data.A.centers) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (G V : M → Space), ContMDiff planeModel spaceModel ∞ G →
        ContMDiff planeModel spaceModel ∞ V → ∀ b : ℝ, 0 ≤ b → b < ρ →
      data.A.WeightedBound 1 2 b (G-F) →
      (∀ p ∈ tsupport (data.A.weight i),
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ data.A.vectorPlaneRead i V)
          (planeCoordinateIsometry (chart (i : M) p))) ∧
        realSecondTensor (spaceCoordinates ∘ data.A.vectorPlaneRead i V)
          (planeCoordinateIsometry (chart (i : M) p)) ≠ 0) →
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
    obtain ⟨ξ,Q,_,_,hgood,_⟩ := PhaseGeometry.positive_good_phase_data hN
      (H₀ := ![(1:ℝ),0,1]) (by simp) (by simp)
    exact ⟨i,hp,hD,ξ 0,hgood 0⟩
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
