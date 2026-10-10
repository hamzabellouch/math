import OAI.Geometry.SurfaceImmersion.Atlas.ChartGermImmersion
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! A regular point of a smooth surface map has a neighborhood on which
the map is injective. Only the two-to-three-dimensional case is needed. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma euclidean_surface_local_injective {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (p : Base) (hp : Function.Injective (fderiv ℝ f p)) :
    ∃ U : Set Base, IsOpen U ∧ p ∈ U ∧ U.InjOn f := by
  obtain ⟨L,hL⟩ := (fderiv ℝ f p).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hp)
  let R := L.toContinuousLinearMap
  let g : Base → Base := R ∘ f
  have hg : ContDiff ℝ ∞ g := R.contDiff.comp hf
  have hcomp : R.comp (fderiv ℝ f p) = ContinuousLinearMap.id ℝ Base := by
    apply ContinuousLinearMap.ext
    intro v
    exact LinearMap.congr_fun hL v
  have hd : HasFDerivAt g (ContinuousLinearEquiv.refl ℝ Base).toContinuousLinearMap p := by
    have h := R.hasFDerivAt.comp p (hf.differentiable (by simp) p).hasFDerivAt
    rw [hcomp] at h
    exact h
  let e := hg.contDiffAt.toOpenPartialHomeomorph g hd (by simp)
  refine ⟨e.source,e.open_source,hg.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp),?_⟩
  intro x hx y hy hxy
  exact e.injOn hx hy (congrArg R hxy)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_immersion_local_injective {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) (p : M)
    (hp : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U.InjOn f := by
  let a := chart p p
  have hps : p ∈ (chart p).source := by simpa only [chart_source] using mem_chart_source Plane p
  have haT : a ∈ (chart p).target := (chart p).map_source hps
  have hlocal : ContDiffOn ℝ ∞ (f ∘ (chart p).symm) (chart p).target :=
    (hf.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  obtain ⟨W,hW,haW,_hWT,φ,hφ,hmatch⟩ :=
    CollarVelocity.compact_smooth_extension (isCompact_singleton : IsCompact ({a} : Set Base))
      (chart p).open_target (by simpa using haT) hlocal
  have hpmodel : f =ᶠ[𝓝 p] φ ∘ chart p := by
    have ho := (chart p).isOpen_inter_preimage hW
    have haW' : chart p p ∈ W := haW (by rfl)
    filter_upwards [ho.mem_nhds ⟨hps,haW'⟩] with x hx
    have hm := (hmatch hx.2).symm
    change f ((chart p).symm (chart p x)) = φ (chart p x) at hm
    simpa only [Function.comp_apply,(chart p).left_inv hx.1] using hm
  have hi : Function.Injective (fderiv ℝ φ a) :=
    (chart_germ_immersion_iff p hps hφ hpmodel).mp hp
  obtain ⟨O,hO,haO,hφI⟩ := euclidean_surface_local_injective hφ a hi
  let U := (chart p).source ∩ (chart p) ⁻¹' (O ∩ W)
  refine ⟨U,(chart p).isOpen_inter_preimage (hO.inter hW),⟨hps,haO,haW (by rfl)⟩,?_⟩
  intro x hx y hy hxy
  have hxφ : f x = φ (chart p x) := by
    have hh := hmatch hx.2.2
    simpa only [Function.comp_apply,(chart p).left_inv hx.1] using hh.symm
  have hyφ : f y = φ (chart p y) := by
    have hh := hmatch hy.2.2
    simpa only [Function.comp_apply,(chart p).left_inv hy.1] using hh.symm
  apply (chart p).injOn hx.1 hy.1
  apply hφI hx.2.1 hy.2.1
  exact hxφ.symm.trans (hxy.trans hyφ)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
