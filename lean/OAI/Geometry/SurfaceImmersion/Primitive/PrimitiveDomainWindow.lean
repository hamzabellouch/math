import OAI.Geometry.SurfaceImmersion.Primitive.ConstructedPrimitiveSupport

namespace OAI

/-! The compact coordinate window and exact support location used by the
analytic primitive theorem. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates

 def phaseWindow {V : Set SmallModes.Base} (hV : IsOpen V) : TopologicalSpace.Opens JetPolynomial.Base :=
  ⟨baseEquiv ⁻¹' V,hV.preimage baseEquiv.continuous⟩

lemma phaseWindow_closure {V : Set SmallModes.Base} (hV : IsOpen V) :
    closure (phaseWindow hV : Set JetPolynomial.Base) = baseEquiv ⁻¹' closure V :=
  (baseEquiv.toHomeomorph.preimage_closure V).symm

lemma phaseWindow_compact {V : Set SmallModes.Base} (hV : IsOpen V)
    (hVc : IsCompact (closure V)) : IsCompact (closure (phaseWindow hV : Set JetPolynomial.Base)) := by
  rw [phaseWindow_closure]
  exact baseEquiv.toHomeomorph.isCompact_preimage.mpr hVc

lemma phaseWindow_real_closure {V : Set SmallModes.Base} (hV : IsOpen V) :
    baseEquiv '' closure (phaseWindow hV : Set JetPolynomial.Base) = closure V := by
  rw [phaseWindow_closure]
  exact Set.image_preimage_eq _ baseEquiv.surjective

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseSupport_image_contains (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {K : Set JetPolynomial.Base} (hKt : K ⊆ e.target)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    {y : JetPolynomial.Base} (hy : y ∈ K) :
    ∃ p ∈ A.phaseSurfaceSupport i e K, surfacePhaseChart (i : M) e p = baseEquiv y := by
  obtain ⟨p,hp,hpy⟩ := hKA (mem_image_of_mem e.symm hy)
  have hps := A.weight_support i hp
  refine ⟨p,?_,?_⟩
  · apply subset_closure
    exact ⟨e.symm y,mem_image_of_mem e.symm hy,by rw [← hpy,(chart (i : M)).left_inv hps]⟩
  · change baseEquiv (e (chart (i : M) p)) = baseEquiv y
    rw [hpy,e.right_inv (hKt hy)]

lemma phaseSupport_window (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {K : Set JetPolynomial.Base} (hKt : K ⊆ e.target)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    {V : Set SmallModes.Base} (hV : IsOpen V)
    (hCV : (surfacePhaseChart (i : M) e) '' A.phaseSurfaceSupport i e K ⊆ V) :
    K ⊆ (phaseWindow hV : Set JetPolynomial.Base) := by
  intro y hy
  obtain ⟨p,hp,heq⟩ := A.phaseSupport_image_contains i e hKt hKA hy
  change baseEquiv y ∈ V
  rw [← heq]
  exact hCV (mem_image_of_mem _ hp)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
