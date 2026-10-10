import OAI.Geometry.SurfaceImmersion.Geometry.CompactLinearLowerBound
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadDifferential
import OAI.Geometry.SurfaceImmersion.Geometry.C1ImmersionApproximation
import OAI.Geometry.Immersion.ClosedSurface.AtlasPartition

namespace OAI

/-! One lower bound for the coordinate differentials of every immersion
in a fixed C1 neighborhood. The coordinate cores cover the surface. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_coordinate_metric_lower_bound {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G → A.WeightedBound 1 1 δ (G-F) →
      ∀ i : A.centers, ∀ x ∈ A.coordinateCore i, ∀ v : Base,
        c*‖v‖ ≤ ‖fderiv ℝ (A.vectorChartRead i G) x v‖ := by
  classical
  have hcore (i : A.centers) : A.coordinateCore i ⊆ (A.chartWeightCompact i : Set Base) := by
    rintro x ⟨p,hp,rfl⟩
    exact ⟨p,subset_tsupport _ (A.weightCore_nonzero i hp),rfl⟩
  have hdata (i : A.centers) : ∃ c : ℝ, 0 < c ∧
      ∀ x ∈ A.coordinateCore i, ∀ H : Base →L[ℝ] Space,
        ‖H-fderiv ℝ (A.vectorChartRead i F) x‖ ≤ c → ∀ v, c*‖v‖ ≤ ‖H v‖ := by
    have hcont := ((A.vectorChartRead_smooth i hF).fderiv_right (m := ∞) (by simp)).continuous
    obtain ⟨c,hc,hbound⟩ := compact_injective_lower_bound
      ((A.coordinateCore_compact i).image hcont) (by
        rintro _ ⟨x,hx,rfl⟩
        rw [A.vectorChartRead_fderiv i hF (hcore i hx),
          fderiv_comp_chart_symm (hF.of_le (by simp)) (i : M) (A.coordinateCore_target i hx)]
        exact (hImm _).comp ((chart_mdifferentiable (i : M)).symm.mfderiv_injective
          (A.coordinateCore_target i hx)))
    exact ⟨c,hc,fun x hx => hbound _ (mem_image_of_mem _ hx)⟩
  choose c hc hb using hdata
  choose R hR hr using fun i : A.centers => A.vectorChartRead_bound (V := Space) i 1
  obtain ⟨δ,hδ,_,hδi⟩ := finite_positive_threshold (fun i => c i/(R i+1))
    (fun i => div_pos (hc i) (by have := hR i; positivity))
  obtain ⟨a,ha,_,hai⟩ := finite_positive_threshold c hc
  refine ⟨δ,a,hδ,ha,?_⟩
  intro G hG hclose i x hx v
  have hread := hr i (G-F) 1 δ zero_lt_one le_rfl hδ.le (hG.sub hF) hclose
  have hd := hread 1 le_rfl x (mem_univ x)
  simp only [one_pow,one_mul,iteratedFDerivWithin_univ,norm_iteratedFDeriv_one] at hd
  have he : A.vectorChartRead i (G-F) = A.vectorChartRead i G-A.vectorChartRead i F := by
    funext y
    by_cases hy : y ∈ (chart (i : M)).target <;>
      simp [vectorChartRead,localize,hy,smul_sub]
  rw [he,fderiv_sub ((A.vectorChartRead_smooth i hG).differentiable (by simp) x)
    ((A.vectorChartRead_smooth i hF).differentiable (by simp) x)] at hd
  have hsize : R i*δ ≤ c i := by
    have hRi := hR i
    have he := (le_div_iff₀ (by positivity : 0 < R i+1)).mp (hδi i)
    nlinarith
  exact (mul_le_mul_of_nonneg_right (hai i) (norm_nonneg v)).trans
    (hb i x hx _ (hd.trans hsize) v)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
