import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadDifferential
import OAI.Geometry.SurfaceImmersion.Correction.NormalizedJetCorrection

namespace OAI

/-! Atlas representatives agree on an open neighborhood whenever the outer
cutoff is locally one. This retains nonlinear compositions as genuine germs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma vectorChartRead_germ (i : A.centers) (F : M → Space) {p : M}
    (hp : p ∈ tsupport (A.weight i))
    (ho : A.outer i =ᶠ[𝓝 p] (fun _ => (1 : ℝ))) :
    A.vectorChartRead i F =ᶠ[𝓝 (chart (i : M) p)] F ∘ (chart (i : M)).symm := by
  have hps := A.weight_support i hp
  have hpt := (chart (i : M)).map_source hps
  have ht : Tendsto (chart (i : M)).symm (𝓝 (chart (i : M) p)) (𝓝 p) := by
    have hc := ((chart (i : M)).continuousOn_symm _ hpt).continuousAt
      ((chart (i : M)).open_target.mem_nhds hpt)
    simpa only [(chart (i : M)).left_inv hps] using hc.tendsto
  filter_upwards [(chart (i : M)).open_target.mem_nhds hpt,ho.comp_tendsto ht] with y hy he
  change localize (i : M) (A.outer i) F y = _
  rw [localize,indicator_of_mem hy]
  simp only [Function.comp_apply] at he ⊢
  rw [he,one_pow,one_smul]

lemma localized_vectorChartRead_germ (i : A.centers) (F : M → Space) {p : M}
    (hp : p ∈ tsupport (A.weight i))
    (ho : A.outer i =ᶠ[𝓝 p] (fun _ => (1 : ℝ))) :
    localize (i : M) (A.weight i) F =ᶠ[𝓝 (chart (i : M) p)]
      (fun y => (A.chartWeight i y)^2 • A.vectorChartRead i F y) := by
  have hr := A.vectorChartRead_germ i F hp ho
  filter_upwards [(chart (i : M)).open_target.mem_nhds
    ((chart (i : M)).map_source (A.weight_support i hp)),hr] with y hy he
  simp only [localize,chartWeight,indicator_of_mem hy]
  rw [he]
  rfl

lemma vectorChartRead_normalize_germ (i : A.centers) (F : M → Space) {p : M}
    (hp : p ∈ tsupport (A.weight i))
    (ho : A.outer i =ᶠ[𝓝 p] (fun _ => (1 : ℝ))) :
    A.vectorChartRead i (SphericalJets.radialNormalize ∘ F) =ᶠ[𝓝 (chart (i : M) p)]
      SphericalJets.radialNormalize ∘ A.vectorChartRead i F := by
  have h₁ := A.vectorChartRead_germ i (SphericalJets.radialNormalize ∘ F) hp ho
  have h₂ := A.vectorChartRead_germ i F hp ho
  filter_upwards [h₁,h₂] with y h₁ h₂
  simp only [Function.comp_apply] at h₁ h₂ ⊢
  rw [h₁,h₂]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
