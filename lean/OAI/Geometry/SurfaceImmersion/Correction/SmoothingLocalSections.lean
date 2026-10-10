import OAI.Geometry.SurfaceImmersion.Correction.SmoothingLocalization

namespace OAI

/-! Localization only requires smoothness on the chosen chart. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localize_smooth_on (p : M) {ψ : M → ℝ} (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ)
    (hsupp : tsupport ψ ⊆ (chart p).source) {f : M → V}
    (hf : ContMDiffOn planeModel 𝓘(ℝ, V) ∞ f (chart p).source) :
    ContDiff ℝ ∞ (localize p ψ f) := by
  have hfc := hf.comp (chart_symm_smooth p) (chart p).mapsTo_symm
  have hlocal : ContDiffOn ℝ ∞
      (fun x => (ψ ((chart p).symm x)) ^ 2 • f ((chart p).symm x)) (chart p).target :=
    (((hψ.comp_contMDiffOn (chart_symm_smooth p)).pow 2).smul hfc).contDiffOn
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (localize p ψ f)
  case neg => exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)
  obtain ⟨y, hy, hxy⟩ := localize_tsupport p hsupp f hx
  have hxT : x ∈ (chart p).target := hxy ▸ (chart p).map_source (hsupp hy)
  apply (hlocal.contDiffAt ((chart p).open_target.mem_nhds hxT)).congr_of_eventuallyEq
  filter_upwards [(chart p).open_target.mem_nhds hxT] with z hz
  exact indicator_of_mem hz _

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
