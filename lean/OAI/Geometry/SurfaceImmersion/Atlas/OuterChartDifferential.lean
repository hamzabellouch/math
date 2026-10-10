import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadDifferential

namespace OAI

/-! Recover the actual differential wherever the outer chart cutoff equals
one on a neighborhood, including a collar beyond the primitive support. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma vectorChartRead_comp_chart_of_outer (i : A.centers) (F : M → Space)
    {p : M} (hp : p ∈ (chart (i : M)).source)
    (houter : A.outer i =ᶠ[𝓝 p] fun _ => (1 : ℝ)) :
    F =ᶠ[𝓝 p] A.vectorChartRead i F ∘ chart (i : M) := by
  filter_upwards [(chart (i : M)).open_source.mem_nhds hp,houter] with q hq hone
  simp only [Function.comp_apply,vectorChartRead,localize,
    indicator_of_mem ((chart (i : M)).map_source hq),
    (chart (i : M)).left_inv hq,hone,one_pow,one_smul]

lemma vectorChartRead_differential_of_outer (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {p : M} (hp : p ∈ (chart (i : M)).source)
    (houter : A.outer i =ᶠ[𝓝 p] fun _ => (1 : ℝ)) :
    surfaceDifferential F p = (fderiv ℝ (A.vectorChartRead i F) (chart (i : M) p)).comp
      (surfaceDifferential (chart (i : M)) p) := by
  have hc := ((chart_smooth (i : M)) p hp).contMDiffAt
    ((chart (i : M)).open_source.mem_nhds hp)
  have he := A.vectorChartRead_comp_chart_of_outer i F hp houter
  unfold surfaceDifferential
  rw [he.mfderiv_eq,mfderiv_comp p
    ((A.vectorChartRead_smooth i hF).differentiable (by simp) _).mdifferentiableAt
    (hc.mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
