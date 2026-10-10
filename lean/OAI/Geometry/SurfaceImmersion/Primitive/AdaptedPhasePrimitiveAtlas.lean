import OAI.Geometry.SurfaceImmersion.Atlas.PrescribedAtlasPlateau
import OAI.Geometry.SurfaceImmersion.Atlas.SurfacePhaseCharts
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasSupportedWeights
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

namespace OAI

/-! Restrict the primitive's phase domain and choose its analytic atlas
inside the already prepared exterior collar. The phase functions are unchanged. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem adapted_phase_primitive_atlas (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {K : Set M} (hK : IsCompact K) (hqK : q ∈ K)
    (hKs : K ⊆ (surfacePhaseChart q e).source)
    {V : Set Base} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hKV : (surfacePhaseChart q e) '' K ⊆ V)
    (hVs : closure V ⊆ (surfacePhaseChart q e).target) :
    ∃ (A : SmoothingAtlas M) (i : A.centers)
      (f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base),
      (i : M) = q ∧ (∀ x, f x = e x) ∧ (∀ x, f.symm x = e.symm x) ∧
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ f.symm ∧
      (∀ p ∈ K, 0 < A.weight i p) ∧
      (∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1)) ∧
      (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ f.source ∧
      MapsTo f f.source (baseEquiv ⁻¹' V) ∧
      K ⊆ (surfacePhaseChart (i : M) f).source ∧
      ∀ x ∈ closure V, A.outer i =ᶠ[𝓝 ((surfacePhaseChart q e).symm x)] (fun _ => 1) := by
  let E := surfacePhaseChart q e
  let U := E.source ∩ E ⁻¹' V
  have hU : IsOpen U := E.isOpen_inter_preimage hV
  have hKU : K ⊆ U := fun p hp => ⟨hKs hp,hKV (mem_image_of_mem E hp)⟩
  let P := E.symm '' closure V
  have hP : IsCompact P := hVc.image_of_continuousOn (E.symm.continuousOn.mono hVs)
  have hPs : P ⊆ (chart q).source := by
    rintro _ ⟨x,hx,rfl⟩
    exact (E.map_target (hVs hx)).1
  obtain ⟨A,i,hiq,hpos,hweight,ho,hplateau⟩ := exists_smoothingAtlas_prescribed_plateau q
    hK hqK hU hKU (fun _ hp => hp.1.1) hP hPs
  let W := (fun x : JetPolynomial.Base => baseEquiv (e x)) ⁻¹' V
  have hW : IsOpen W := hV.preimage (baseEquiv.continuous.comp he.continuous)
  let f := e.restrOpen W hW
  have hsource : (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ f.source := by
    rintro x ⟨p,hp,rfl⟩
    have hpU := hweight hp
    change chart (i : M) p ∈ e.source ∩ W
    rw [hiq]
    exact ⟨hpU.1.2,hpU.2⟩
  refine ⟨A,i,f,hiq,(fun _ => rfl),(fun _ => rfl),he,hi,hpos,ho,hsource,?_,?_,?_⟩
  · intro x hx
    exact hx.2
  · intro p hp
    have hu := hKU hp
    change p ∈ (chart (i : M)).source ∧ chart (i : M) p ∈ f.source
    rw [hiq]
    exact ⟨hu.1.1,hu.1.2,hu.2⟩
  · intro x hx
    exact hplateau _ ⟨x,hx,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
