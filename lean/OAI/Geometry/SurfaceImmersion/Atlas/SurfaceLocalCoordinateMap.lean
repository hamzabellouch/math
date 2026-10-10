import OAI.Geometry.SurfaceImmersion.Atlas.RegularPlaneChart
import OAI.Geometry.SurfaceImmersion.Correction.SmoothingAtlas

namespace OAI

/-! A smooth surface-to-plane map with invertible derivative is an
actual smooth local coordinate chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_local_coordinate_map {f : M → Base}
    (hf : ContMDiff planeModel 𝓘(ℝ,Base) ∞ f) (p : M)
    (hp : Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) f p)) :
    ∃ d : OpenPartialHomeomorph M Base, p ∈ d.source ∧ EqOn d f d.source ∧
      ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ d d.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d.symm d.target := by
  let c := chart p
  let a := c p
  have hpc : p ∈ c.source := by simpa only [c,chart_source] using mem_chart_source Plane p
  have ha : a ∈ c.target := c.map_source hpc
  have hlocal : ContDiffOn ℝ ∞ (f ∘ c.symm) c.target :=
    (hf.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  obtain ⟨V,hV,haV,hVc,φ,hφ,hφEq⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := a)) c.open_target (singleton_subset_iff.mpr ha) hlocal
  have haV' : a ∈ V := haV (mem_singleton _)
  have heφ : φ =ᶠ[𝓝 a] f ∘ c.symm := hφEq.eventuallyEq_of_mem (hV.mem_nhds haV')
  have hcp : c.symm a = p := c.left_inv hpc
  have hcD : c.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨(chart_symm_smooth p).mdifferentiableOn (by simp),(chart_smooth p).mdifferentiableOn (by simp)⟩
  have hφbij : Function.Bijective (fderiv ℝ φ a) := by
    rw [heφ.fderiv_eq,← mfderiv_eq_fderiv,mfderiv_comp a
      (hf.mdifferentiable (by simp) _) (hcD.mdifferentiableAt ha)]
    exact (hcp.symm ▸ hp).comp (hcD.mfderiv_bijective ha)
  obtain ⟨e,hae,he,hei⟩ := regular_plane_chart hφ a hφbij
  let d₀ := c.trans e
  let O := c.source ∩ c ⁻¹' V
  have hO : IsOpen O := c.isOpen_inter_preimage hV
  let d := d₀.restrOpen O hO
  have hps : p ∈ d.source := ⟨⟨hpc,hae⟩,hpc,haV'⟩
  have hds₀ : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ d₀ d₀.source :=
    (he ▸ hφ.contMDiff).comp_contMDiffOn ((chart_smooth p).mono inter_subset_left)
  have hdi₀ : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d₀.symm d₀.target :=
    (chart_symm_smooth p).comp (hei.contMDiffOn.mono inter_subset_left) (fun _ hx => hx.2)
  refine ⟨d,hps,?_,hds₀.mono (fun _ hx => hx.1),hdi₀.mono (fun _ hx => hx.1)⟩
  intro x hx
  change e (c x) = f x
  rw [he,hφEq hx.2.2]
  change f (c.symm (c x)) = f x
  rw [c.left_inv hx.1.1]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
