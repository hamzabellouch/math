import OAI.Geometry.SurfaceImmersion.Atlas.PlaneCurveCoordinates
import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceChartRepresentative

namespace OAI

/-! A regular smooth curve in the surface is the second coordinate
in actual smooth local surface coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_curve_coordinates {γ : ℝ → M} {I : Set ℝ}
    (hI : IsOpen I) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ I) {t : ℝ} (ht : t ∈ I)
    (hreg : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t)) :
    ∃ (c : OpenPartialHomeomorph M Base) (U : Set ℝ),
      IsOpen U ∧ t ∈ U ∧ U ⊆ I ∧
      ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target ∧
      ∀ s ∈ U, γ s ∈ c.source ∧ c (γ s) = ![0,s] := by
  let p := γ t
  have hp : p ∈ (chart p).source := by
    simpa only [chart_source] using mem_chart_source Plane p
  let W := I ∩ γ ⁻¹' (chart p).source
  have hW : IsOpen W := hγ.continuousOn.isOpen_inter_preimage hI (chart p).open_source
  have htW : t ∈ W := ⟨ht,hp⟩
  have hγt := hγ.contMDiffAt (hI.mem_nhds ht)
  let φ : ℝ → Base := chart p ∘ γ
  have hφ : ContDiffOn ℝ ∞ φ W :=
    ((chart_smooth p).comp (hγ.mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn
  have hφI : Function.Injective (fderiv ℝ φ t) := by
    have hc := ((chart_smooth p).contMDiffAt ((chart p).open_source.mem_nhds hp))
    rw [← mfderiv_eq_fderiv,mfderiv_comp t (hc.mdifferentiableAt (by simp))
      (hγt.mdifferentiableAt (by simp))]
    exact ((chart_mdifferentiable p).mfderiv_injective hp).comp hreg
  obtain ⟨V,hV,htV,hVW,F,hF,hFφ⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := t)) hW (singleton_subset_iff.mpr htW) hφ
  have hFe : F =ᶠ[𝓝 t] φ := hFφ.eventuallyEq_of_mem (hV.mem_nhds (htV (by simp)))
  have hFI : Function.Injective (fderiv ℝ F t) := by rw [hFe.fderiv_eq]; exact hφI
  have hFt : deriv F t ≠ 0 := by
    intro hz
    have he : fderiv ℝ F t 1 = fderiv ℝ F t 0 := by
      rw [fderiv_apply_one_eq_deriv,hz,map_zero]
    have hn := hFI he
    norm_num at hn
  obtain ⟨e,J,hJ,htJ,hes,hei,heaxis⟩ := plane_curve_coordinates hF t hFt
  let c := (chart p).trans e.symm
  have hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source := by
    exact hei.contMDiffOn.comp ((chart_smooth p).mono inter_subset_left) (fun _ hx => hx.2)
  have hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target := by
    exact (chart_symm_smooth p).comp hes.contMDiff.contMDiffOn (fun _ hx => hx.2)
  refine ⟨c,V ∩ J,hV.inter hJ,⟨htV (by simp),htJ⟩,
    inter_subset_left.trans (hVW.trans inter_subset_left),hcs,hci,?_⟩
  intro s hs
  have hsW := hVW hs.1
  have hmodel : e ![0,s] = chart p (γ s) := (heaxis s hs.2).2.trans (hFφ hs.1)
  have hsource : γ s ∈ c.source := by
    refine ⟨hsW.2,?_⟩
    change chart p (γ s) ∈ e.target
    rw [← hmodel]
    exact e.map_source (heaxis s hs.2).1
  refine ⟨hsource,?_⟩
  change e.symm (chart p (γ s)) = ![0,s]
  rw [← hmodel]
  exact e.left_inv (heaxis s hs.2).1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
