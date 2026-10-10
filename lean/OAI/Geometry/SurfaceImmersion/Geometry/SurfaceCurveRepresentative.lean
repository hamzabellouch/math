import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceCurveCoordinates

namespace OAI

/-! A regular surface curve has an actual smooth Euclidean representative
in any selected surface chart through its base point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_curve_chart_representative {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ U)
    {t : ℝ} (ht : t ∈ U) (p : M) (hp : γ t ∈ (chart p).source)
    (hr : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t)) :
    ∃ (F : ℝ → Base) (V : Set ℝ), ContDiff ℝ ∞ F ∧ IsOpen V ∧ t ∈ V ∧ V ⊆ U ∧
      (∀ u ∈ V, γ u ∈ (chart p).source ∧ F u = chart p (γ u)) ∧ deriv F t ≠ 0 := by
  let W := U ∩ γ ⁻¹' (chart p).source
  have hW : IsOpen W := hγ.continuousOn.isOpen_inter_preimage hU (chart p).open_source
  have htW : t ∈ W := ⟨ht,hp⟩
  let φ : ℝ → Base := chart p ∘ γ
  have hφ : ContDiffOn ℝ ∞ φ W :=
    ((chart_smooth p).comp (hγ.mono inter_subset_left) (fun _ hu => hu.2)).contDiffOn
  obtain ⟨V,hV,htV,hVW,F,hF,hFφ⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := t)) hW (singleton_subset_iff.mpr htW) hφ
  have he : F =ᶠ[𝓝 t] φ := hFφ.eventuallyEq_of_mem (hV.mem_nhds (htV (by simp)))
  have hφi : Function.Injective (fderiv ℝ φ t) := by
    rw [← mfderiv_eq_fderiv,mfderiv_comp t
      (((chart_smooth p).contMDiffAt ((chart p).open_source.mem_nhds hp)).mdifferentiableAt (by simp))
      ((hγ.contMDiffAt (hU.mem_nhds ht)).mdifferentiableAt (by simp))]
    exact ((chart_mdifferentiable p).mfderiv_injective hp).comp hr
  have hFi : Function.Injective (fderiv ℝ F t) := by rw [he.fderiv_eq]; exact hφi
  have hFn : deriv F t ≠ 0 := by
    intro hz
    have h01 : fderiv ℝ F t 1 = fderiv ℝ F t 0 := by
      rw [fderiv_apply_one_eq_deriv,hz,map_zero]
    have hn := hFi h01
    norm_num at hn
  refine ⟨F,V,hF,hV,htV (by simp),hVW.trans inter_subset_left,?_,hFn⟩
  intro u hu
  exact ⟨(hVW hu).2,hFφ hu⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
