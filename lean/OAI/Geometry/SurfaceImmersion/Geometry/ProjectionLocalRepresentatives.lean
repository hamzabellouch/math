import OAI.Geometry.SurfaceImmersion.Whitney.FiniteSingularProjection
import OAI.Geometry.SurfaceImmersion.Atlas.WeightedProjectionLinearization
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! Globally smooth representatives for the original immersion in each
active coordinate core, with the exact weighted-jet germ. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exists_projection_representatives {F : M → ProjectionTarget 3 × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) ∞ F) :
    ∃ Φ : A.centers → Base → ProjectionTarget 3 × ℝ,
      (∀ i, ContDiff ℝ ∞ (Φ i)) ∧
      ∀ i x, x ∈ A.coordinateCore i →
        Φ i =ᶠ[𝓝 x] F ∘ (chart (i : M)).symm := by
  have hc (i : A.centers) : ContDiffOn ℝ ∞
      (F ∘ (chart (i : M)).symm) (chart (i : M)).target :=
    (hF.comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn
  choose U hU hKU _ Φ hΦ hEq using fun i =>
    CollarVelocity.compact_smooth_extension (A.coordinateCore_compact i)
      (chart (i : M)).open_target (A.coordinateCore_target i) (hc i)
  refine ⟨Φ,hΦ,?_⟩
  intro i x hx
  filter_upwards [(hU i).mem_nhds (hKU i hx)] with y hy
  exact hEq i hy

omit [CompactSpace M] in
lemma localizedWeight_ne_zero_on_core (i : A.centers) {x : Base}
    (hx : x ∈ A.coordinateCore i) : localizedWeight (i : M) (A.weight i) x ≠ 0 := by
  have hxT := A.coordinateCore_target i hx
  have hw := A.coordinateCore_weight_nonzero i hx
  simpa only [localizedWeight,localize,indicator_of_mem hxT,smul_eq_mul,mul_one]
    using pow_ne_zero 2 hw

theorem projectionJet_representative_germ {F : M → ProjectionTarget 3 × ℝ}
    (i : A.centers) {Φ : Base → ProjectionTarget 3 × ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {x : Base} (hx : x ∈ A.coordinateCore i)
    (he : Φ =ᶠ[𝓝 x] F ∘ (chart (i : M)).symm) :
    A.projectionJet F i =ᶠ[𝓝 x] fun y =>
      (localizedWeight (i : M) (A.weight i) y)^2 • fderiv ℝ Φ y := by
  have hp : localize (i : M) (A.weight i) F =ᶠ[𝓝 x]
      fun y => localizedWeight (i : M) (A.weight i) y • Φ y := by
    filter_upwards [he,(chart (i : M)).open_target.mem_nhds (A.coordinateCore_target i hx)]
      with y hy hyT
    simp only [localizedWeight,localize,indicator_of_mem hyT,smul_eq_mul,mul_one,hy]
    rfl
  exact weightedJet_product_germ
    (localizedWeight_smooth (i : M) (A.weight_smooth i) (A.weight_support i)) hΦ hp

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
