import OAI.Geometry.SurfaceImmersion.Atlas.AtlasSecondFormMargin
import OAI.Geometry.SurfaceImmersion.Atlas.ChartSecondFormBounds
import OAI.Geometry.SurfaceImmersion.Primitive.SupportedPrimitiveGeometry

namespace OAI

/-! The primitive's transverse margin and exterior convergence give a
uniform second-form lower bound in every chart of the fixed atlas. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

theorem primitive_atlas_normal_margin (data : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) (i : data.A.centers) {c : ℝ} (hc : 0 < c) :
    ∃ ρ c₀ : ℝ, 0 < ρ ∧ 0 < c₀ ∧
      ∀ (G V : M → Space), ContMDiff planeModel spaceModel ∞ G →
        ContMDiff planeModel spaceModel ∞ V →
      (∀ p, Function.Injective (mfderiv planeModel spaceModel V p)) →
      ∀ b : ℝ, 0 ≤ b → b < ρ → data.A.WeightedBound 1 2 b (G-F) →
      (∀ p ∈ tsupport (data.A.weight i),
        c < ‖realSecondTensor (spaceCoordinates ∘ data.A.vectorPlaneRead i V)
          (planeCoordinateIsometry (chart (i : M) p))‖) →
      (∀ p ∉ tsupport (data.A.weight i), V =ᶠ[𝓝 p] G) →
      ∀ j x, x ∈ (modeSupport (data.A.chartWeightCompact j) : Set SmallModes.Base) →
        c₀ < ‖realSecondTensor (spaceCoordinates ∘ data.A.vectorPlaneRead j V) x‖ := by
  classical
  obtain ⟨ρ,ce,hρ,hce,hextbound⟩ := data.uniform_secondForm_C2_margin hF
  let K (j : data.A.centers) := tsupport (data.A.weight j) ∩ tsupport (data.A.weight i)
  have hK (j : data.A.centers) : IsCompact (K j) :=
    ((isClosed_tsupport _).inter (isClosed_tsupport _)).isCompact
  have hKs (j : data.A.centers) : K j ⊆ (coordinateChart (i : M)).source := by
    intro p hp
    simpa only [coordinateChart_source,chart_source] using data.A.weight_support i hp.2
  have hKt (j : data.A.centers) : K j ⊆ (coordinateChart (j : M)).source := by
    intro p hp
    simpa only [coordinateChart_source,chart_source] using data.A.weight_support j hp.1
  choose C hC hcompare using fun j => compact_overlap_secondTensor_bound (hK j)
    (j : M) (i : M) (hKs j) (hKt j)
  let C₀ := 1+∑ j, C j
  have hsum : 0 ≤ ∑ j, C j := Finset.sum_nonneg (fun j _ => (hC j).le)
  have hC₀ : 0 < C₀ := by
    change 0 < 1+∑ j, C j
    linarith
  have hCC (j : data.A.centers) : C j ≤ C₀ := by
    have hh := Finset.single_le_sum (fun k _ => (hC k).le) (Finset.mem_univ j)
    change C j ≤ 1+∑ j, C j
    linarith
  refine ⟨ρ,min ce (c/C₀),hρ,lt_min hce (div_pos hc hC₀),?_⟩
  intro G V hG hV hI b hb hbρ hclose hlocal hexterior j x hx
  obtain ⟨y,⟨p,hp,rfl⟩,rfl⟩ := hx
  have hpoint (k : data.A.centers) :
      coordinateChart (k : M) p = planeCoordinateIsometry (chart (k : M) p) := by
    rw [planeCoordinateIsometry_chart]
    rfl
  by_cases hpi : p ∈ tsupport (data.A.weight i)
  · have hxi : coordinateChart (j : M) p ∈ coordinateDomain (j : M) := by
      rw [← coordinateChart_target]
      exact (coordinateChart (j : M)).map_source (by
        simpa only [coordinateChart_source,chart_source] using data.A.weight_support j hp)
    have hcmp := hcompare j V hV p ⟨hp,hpi⟩
      (coordinateMap_injective_of_immersion hV hI (j : M) hxi)
    have hei := (realSecondTensor_eventuallyEq
      (data.A.vectorPlaneRead_eventually_coordinateMap V i (data.outer_locally_one i) hpi)).eq_of_nhds
    have hej := (realSecondTensor_eventuallyEq
      (data.A.vectorPlaneRead_eventually_coordinateMap V j (data.outer_locally_one j) hp)).eq_of_nhds
    rw [hpoint i,hpoint j,← hei,← hej] at hcmp
    have hnorm := (hlocal p hpi).trans_le (hcmp.trans
      (mul_le_mul_of_nonneg_right (hCC j) (norm_nonneg _)))
    exact (min_le_right _ _).trans_lt ((div_lt_iff₀ hC₀).mpr (by
      simpa only [mul_comm] using hnorm))
  · have he := data.A.planeRead_eventuallyEq_on_weight (hexterior p hpi) j hp
      (data.outer_locally_one j)
    rw [(realSecondTensor_eventuallyEq he).eq_of_nhds]
    exact (min_le_left _ _).trans_lt (hextbound G hG b hb hbρ hclose j _
      ⟨chart (j : M) p,⟨p,hp,rfl⟩,rfl⟩)

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
