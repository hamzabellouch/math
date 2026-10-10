import OAI.Geometry.SurfaceImmersion.Geometry.ScalarNonflatCriticalValues
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! A global critical-value theorem also applies to smooth maps on open
coordinate domains, by a compactly supported local extension. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F]

theorem local_critical_values_null (μ : Measure F)
    (hglobal : ∀ f : E → F, ContDiff ℝ ∞ f →
      μ (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0)
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    μ (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  apply null_image_of_locally_null
  intro p hp
  obtain ⟨W,hW,hpW,hWU,g,hg,hgf⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := p)) hU (singleton_subset_iff.mpr hp.1) hf
  refine ⟨W,hW,hpW (mem_singleton p),measure_mono_null ?_ (hglobal g hg)⟩
  rintro y ⟨x,⟨hx,hxW⟩,rfl⟩
  have he : g =ᶠ[𝓝 x] f := Filter.eventuallyEq_iff_exists_mem.mpr ⟨W,hW.mem_nhds hxW,hgf⟩
  refine ⟨x,?_,hgf hxW⟩
  change ¬ Function.Surjective (fderiv ℝ g x)
  rw [he.fderiv_eq (𝕜 := ℝ)]
  exact hx.2

theorem scalar_surface_local_critical_values_null {f : JetPolynomial.Base → ℝ}
    {U : Set JetPolynomial.Base} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  apply local_critical_values_null volume ?_ hU hf
  intro g hg
  apply measure_mono_null (image_mono ?_) (scalar_surface_critical_values_null hg)
  intro x hx
  by_contra hn
  exact hx (surjective_of_nonzero_of_finrank_eq_one
    (by simp : Module.finrank ℝ ℝ = 1)
    (show (fderiv ℝ g x).toLinearMap ≠ 0 from fun h => hn (by ext v; exact congrArg (fun L => L v) h)))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
