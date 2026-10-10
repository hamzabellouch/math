import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapAxisCurve
import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceCurveCoordinates

namespace OAI

/-! Regularity under smooth reparameterization and actual curve germs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma regular_curve_germ {γ δ : ℝ → M} {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ) planeModel ∞ γ t) (he : δ =ᶠ[𝓝 t] γ)
    (hi : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t)) :
    Function.Injective (mfderiv 𝓘(ℝ) planeModel δ t) := by
  have hD := ((hγ.mdifferentiableAt (by simp)).hasMFDerivAt.congr_of_eventuallyEq_abuse he).mfderiv
  exact hD.symm ▸ hi

lemma regular_curve_reparameterization {γ : ℝ → M} (e : ℝ ≃ₜ ℝ)
    (hes : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ) planeModel ∞ γ (e t))
    (hi : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ (e t))) :
    Function.Injective (mfderiv 𝓘(ℝ) planeModel (γ ∘ e) t) := by
  have heD : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ) 𝓘(ℝ) :=
    ⟨hes.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn,
      hei.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn⟩
  rw [mfderiv_comp t (hγ.mdifferentiableAt (by simp)) (hes.contMDiff.mdifferentiable (by simp) t)]
  exact hi.comp (heD.mfderiv_injective (mem_univ t))

variable [IsManifold planeModel ∞ M]

lemma regular_curve_neighborhood {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ U) {t : ℝ}
    (ht : t ∈ U) (hi : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t)) :
    ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧ V ⊆ U ∧
      ∀ s ∈ V, Function.Injective (mfderiv 𝓘(ℝ) planeModel γ s) := by
  obtain ⟨c,V,hV,htV,hVU,hcs,hci,hcoord⟩ := surface_curve_coordinates hU hγ ht hi
  have hdif : c.symm.MDifferentiable 𝓘(ℝ,JetPolynomial.Base) planeModel :=
    ⟨hci.mdifferentiableOn (by simp),hcs.mdifferentiableOn (by simp)⟩
  refine ⟨V,hV,htV,hVU,?_⟩
  intro s hs
  have htarget : crosscapAxis s ∈ c.target := by
    rw [crosscapAxis_apply,← (hcoord s hs).2]
    exact c.map_source (hcoord s hs).1
  let δ : ℝ → M := c.symm ∘ crosscapAxis
  have hk : ContMDiff 𝓘(ℝ) 𝓘(ℝ,JetPolynomial.Base) ∞ crosscapAxis := crosscapAxis.contDiff.contMDiff
  have hδ : ContMDiffAt 𝓘(ℝ) planeModel ∞ δ s :=
    (hci.contMDiffAt (c.open_target.mem_nhds htarget)).comp s hk.contMDiffAt
  have hδi : Function.Injective (mfderiv 𝓘(ℝ) planeModel δ s) := by
    rw [mfderiv_comp s
      ((hci.contMDiffAt (c.open_target.mem_nhds htarget)).mdifferentiableAt (by simp))
      (hk.mdifferentiable (by simp) s)]
    exact (hdif.mfderiv_injective htarget).comp (crosscapAxis_regular s)
  apply regular_curve_germ hδ _ hδi
  filter_upwards [hV.mem_nhds hs] with r hr
  change γ r = c.symm (crosscapAxis r)
  rw [crosscapAxis_apply,← (hcoord r hr).2,c.left_inv (hcoord r hr).1]

lemma curve_regular_locus_open {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ U) :
    IsOpen {t | t ∈ U ∧ Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  obtain ⟨V,hV,htV,hVU,hreg⟩ := regular_curve_neighborhood hU hγ ht.1 ht.2
  apply mem_of_superset (hV.mem_nhds htV)
  exact fun s hs => ⟨hVU hs,hreg s hs⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
