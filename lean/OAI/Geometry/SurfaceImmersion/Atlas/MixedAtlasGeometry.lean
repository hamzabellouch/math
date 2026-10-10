import OAI.Geometry.SurfaceImmersion.Geometry.SupportedPatchGeometry
import OAI.Geometry.SurfaceImmersion.Atlas.CrossAtlasBounds

namespace OAI

/-! Local primitive geometry and exterior regularity may use different atlases. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma geometry_at_of_planeRead_good {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (houter : ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (i : A.centers) (p : M) (hp : p ∈ tsupport (A.weight i))
    (hI : Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p))))
    {ξ : SmallModes.Base} (hg : Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p))) ξ) :
    Function.Injective (mfderiv planeModel spaceModel F p) ∧
      ∃ v w : SmallModes.Base, realSecondForm (coordinateMap F p) v w (coordinateCenter p) ≠ 0 := by
  refine ⟨A.immersion_of_planeRead_injective i hF hp hI,?_⟩
  have he := A.vectorPlaneRead_eventually_coordinateMap F i (houter i) hp
  have hpoint : coordinateChart (i : M) p = planeCoordinateIsometry (chart (i : M) p) := by
    rw [planeCoordinateIsometry_chart]
    rfl
  apply nonzero_secondForm_of_chart_good hF (i : M) p
    (by simpa [coordinateChart_source,chart] using A.weight_support i hp)
  · rw [hpoint,← he.fderiv_eq]
    exact hI
  · rw [hpoint,← (realSecondTensor_eventuallyEq he).eq_of_nhds]
    exact hg

end SmoothingAtlas
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

theorem independent_supported_patch_geometry (data : MetricGoodPhaseData g F)
    (B : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (B.weight i) → B.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (i : B.centers) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (G V : M → Space), ContMDiff planeModel spaceModel ∞ G →
        ContMDiff planeModel spaceModel ∞ V → ∀ b : ℝ, 0 ≤ b → b < ρ →
      B.WeightedBound 1 2 b (G-F) →
      (∀ p ∈ tsupport (B.weight i),
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ B.vectorPlaneRead i V)
          (planeCoordinateIsometry (chart (i : M) p))) ∧
        realSecondTensor (spaceCoordinates ∘ B.vectorPlaneRead i V)
          (planeCoordinateIsometry (chart (i : M) p)) ≠ 0) →
      (∀ p ∉ tsupport (B.weight i), V =ᶠ[𝓝 p] G) →
      (∀ p, Function.Injective (mfderiv planeModel spaceModel V p)) ∧
      (∀ p, ∃ v w : SmallModes.Base,
        realSecondForm (coordinateMap V p) v w (coordinateCenter p) ≠ 0) := by
  obtain ⟨ρ,hρ,hnear⟩ := data.uniform_C2_geometry hF
  obtain ⟨D,hD,hchange⟩ := B.weightedBound_change_atlas (V := Space) data.A 2
  have hDp : 0 < D+1 := by positivity
  refine ⟨ρ/(D+1),div_pos hρ hDp,?_⟩
  intro G V hG hV b hb hbr hclose hnormal hexterior
  have hDb : D*b < ρ := by
    have hh := (lt_div_iff₀ hDp).mp hbr
    nlinarith
  obtain ⟨hImm,hgood,_⟩ := hnear G hG (D*b) (mul_nonneg hD hb) hDb
    (hchange (G-F) 1 b zero_lt_one le_rfl hb (hG.sub hF) hclose)
  have hpoint (p : M) : Function.Injective (mfderiv planeModel spaceModel V p) ∧
      ∃ v w : SmallModes.Base, realSecondForm (coordinateMap V p) v w (coordinateCenter p) ≠ 0 := by
    by_cases hp : p ∈ tsupport (B.weight i)
    · obtain ⟨hI,hN⟩ := hnormal p hp
      obtain ⟨ξ,_,_,_,hg,_⟩ := PhaseGeometry.positive_good_phase_data hN
        (H₀ := ![(1:ℝ),0,1]) (by simp) (by simp)
      exact B.geometry_at_of_planeRead_good hV houter i p hp hI (hg 0)
    · obtain ⟨j,hj⟩ : ∃ j : data.A.centers, data.A.weight j p ≠ 0 := by
        by_contra! hz
        have hh := data.A.partition p
        simp only [hz,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at hh
        norm_num at hh
      have hjp : p ∈ tsupport (data.A.weight j) := subset_tsupport _ hj
      have hx : planeCoordinateIsometry (chart (j : M) p) ∈
          (modeSupport (data.A.chartWeightCompact j) : Set SmallModes.Base) :=
        ⟨chart (j : M) p,⟨p,hjp,rfl⟩,rfl⟩
      have he := data.A.planeRead_eventuallyEq_on_weight (hexterior p hp) j hjp
        (data.outer_locally_one j)
      apply data.A.geometry_at_of_planeRead_good hV data.outer_locally_one j p hjp
      · rw [he.fderiv_eq]
        exact hImm j _ hx
      · rw [(realSecondTensor_eventuallyEq he).eq_of_nhds]
        exact hgood j 0 _ hx
  exact ⟨fun p => (hpoint p).1,fun p => (hpoint p).2⟩

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
