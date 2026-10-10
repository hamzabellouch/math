import OAI.Geometry.SurfaceImmersion.Primitive.PrimitivePatchCurves
import OAI.Geometry.SurfaceImmersion.Primitive.CircularPatchDefiners
import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceRealPhaseChart

namespace OAI

/-! The generic circular tangencies supply the actual patch's local definers. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {A B : SmoothingAtlas M} {i : A.centers}
  {e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base}
  {F : M → Space} {amp phi : M → ℝ} {D : Set M}
namespace SupportedPrimitivePatch

lemma circular_definers (d : SupportedPrimitivePatch A i e F amp phi D)
    (ell : Base) (L R : ℝ) (hR : 0 < R)
    (hD : D = circularCoordinateDisk (i : M) R)
    (hphase : ∀ x, (JetPolynomial.realPhaseChart e x).1 =
      centeredConvexPhase ell L (coordinateChart (i : M) i) x)
    (hreg : circularCoordinateRegion (i : M) R ⊆ (coordinateChart (i : M)).target)
    {ι : Type*} [Fintype ι] (curves : ι → PhaseBoundaryCurve B)
    (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (hcarrier : ∀ j, (curves j).carrier = circularBoundary ((curves j).index : M) (r j))
    (hregions : ∀ j, circularCoordinateRegion ((curves j).index : M) (r j) ⊆
      (coordinateChart ((curves j).index : M)).target)
    (E₀ : Set M) (hE₀ : E₀.Finite)
    (hcross : ∀ j k, j ≠ k → (curves j).carrier ∩ (curves k).carrier ⊆ E₀)
    (htan : ∀ j, (circularPhaseTangencies (i : M) ((curves j).index : M)
      ell L (r j) R).Finite) :
    ∃ P : Set Base, P.Finite ∧ ∀ p ∈ (⋃ j, d.curve (curves j)) \ P,
      ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧ ∃ f : Base → ℝ,
        ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ (⋃ j, d.curve (curves j)) ∩ N, f x = 0) ∧
        fderiv ℝ f p dy ≠ 0 := by
  have hcl : closure D = circularDiskClosure (i : M) R := by
    rw [hD,circularCoordinateDisk_closure (i : M) hR hreg]
  have hc : circularDiskClosure (i : M) R ⊆
      ((coordinateChart (i : M)).trans (JetPolynomial.realPhaseChart e)).source := by
    rw [← surfacePhaseChart_real_source,← hcl]
    exact d.source_closed
  have hC (j : ι) : d.curve (curves j) =
      ((coordinateChart (i : M)).trans (JetPolynomial.realPhaseChart e)) ''
        (circularBoundary ((curves j).index : M) (r j) ∩ circularDiskClosure (i : M) R) := by
    change (surfacePhaseChart (i : M) e) '' ((curves j).carrier ∩ closure D) = _
    rw [hcarrier,hcl]
    congr 1
    funext p
    exact surfacePhaseChart_real_apply (i : M) p e
  obtain ⟨_,P,hP,hlocal⟩ := circular_phase_defining_family_local (i : M) ell L R
    (JetPolynomial.realPhaseChart e) (JetPolynomial.realPhaseChart_smooth e d.phase_smooth)
    (JetPolynomial.realPhaseChart_symm_smooth e d.inverse_smooth) hphase hreg hc
    (fun j => ((curves j).index : M)) r hr hregions E₀ hE₀
    (fun j k hjk => by simpa only [← hcarrier] using hcross j k hjk) htan
  refine ⟨P,hP,?_⟩
  simpa only [hC] using hlocal

end SupportedPrimitivePatch
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
