import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceCurveRepresentative
import OAI.Geometry.SurfaceImmersion.Geometry.CommonCurveGraphs

namespace OAI

/-! Actual common smooth surface coordinates and graph representatives
for two regular curve germs meeting at one surface point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem common_surface_curve_graphs {γ δ : ℝ → M} {A B : Set ℝ}
    (hA : IsOpen A) (hB : IsOpen B)
    (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ A) (hδ : ContMDiffOn 𝓘(ℝ) planeModel ∞ δ B)
    {s t : ℝ} (hs : s ∈ A) (ht : t ∈ B) (hpoint : γ s = δ t)
    (hγr : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ s))
    (hδr : Function.Injective (mfderiv 𝓘(ℝ) planeModel δ t)) :
    ∃ (c : OpenPartialHomeomorph M Base) (g h : ℝ → ℝ) (U V : Set ℝ),
      ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target ∧
      ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧ IsOpen U ∧ IsOpen V ∧
      s ∈ U ∧ t ∈ V ∧ U ⊆ A ∧ V ⊆ B ∧
      (∀ u ∈ U, γ u ∈ c.source ∧ c (γ u) = ![c (γ u) 0,g (c (γ u) 0)]) ∧
      (∀ v ∈ V, δ v ∈ c.source ∧ c (δ v) = ![c (δ v) 0,h (c (δ v) 0)]) ∧
      deriv (fun u => c (γ u) 0) s ≠ 0 ∧ deriv (fun v => c (δ v) 0) t ≠ 0 := by
  let p := γ s
  have hp : γ s ∈ (chart p).source := by
    simpa only [p,chart_source] using mem_chart_source Plane (γ s)
  have hp' : δ t ∈ (chart p).source := hpoint ▸ hp
  obtain ⟨F,I,hF,hI,hsI,hIA,hFI,hFr⟩ := surface_curve_chart_representative hA hγ hs p hp hγr
  obtain ⟨G,J,hG,hJ,htJ,hJB,hGJ,hGr⟩ := surface_curve_chart_representative hB hδ ht p hp' hδr
  obtain ⟨e,g,h,U,V,hg,hh,hU,hV,hsU,htV,hFg,hGh,hFd,hGd⟩ := common_curve_graphs hF hG hFr hGr
  let c := (chart p).trans e.toHomeomorph.toOpenPartialHomeomorph
  have hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source :=
    e.contDiff.contMDiff.comp_contMDiffOn ((chart_smooth p).mono inter_subset_left)
  have hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target :=
    (chart_symm_smooth p).comp e.symm.contDiff.contMDiff.contMDiffOn (fun _ hx => hx.2)
  refine ⟨c,g,h,I ∩ U,J ∩ V,hcs,hci,hg,hh,hI.inter hU,hJ.inter hV,
    ⟨hsI,hsU⟩,⟨htJ,htV⟩,inter_subset_left.trans hIA,inter_subset_left.trans hJB,?_,?_,?_,?_⟩
  · intro u hu
    refine ⟨⟨(hFI u hu.1).1,mem_univ _⟩,?_⟩
    have he := hFg u hu.2
    rw [(hFI u hu.1).2] at he
    exact he
  · intro v hv
    refine ⟨⟨(hGJ v hv.1).1,mem_univ _⟩,?_⟩
    have he := hGh v hv.2
    rw [(hGJ v hv.1).2] at he
    exact he
  · have he : (fun u => c (γ u) 0) =ᶠ[𝓝 s] (fun u => e (F u) 0) := by
      filter_upwards [hI.mem_nhds hsI] with u hu
      change e (chart p (γ u)) 0 = e (F u) 0
      rw [(hFI u hu).2]
    rw [he.deriv_eq]
    exact hFd
  · have he : (fun v => c (δ v) 0) =ᶠ[𝓝 t] (fun v => e (G v) 0) := by
      filter_upwards [hJ.mem_nhds htJ] with v hv
      change e (chart p (δ v)) 0 = e (G v) 0
      rw [(hGJ v hv).2]
    rw [he.deriv_eq]
    exact hGd

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
