import OAI.Geometry.SurfaceImmersion.Primitive.PhasePrimitiveSupport

namespace OAI

/-! Identify the analytic support with the closed geometric primitive disk. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseSurfaceSupport_image (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {C : Set M} (hC : IsClosed C) (hchart : C ⊆ (chart (i : M)).source)
    (hphase : (chart (i : M)) '' C ⊆ e.source) :
    A.phaseSurfaceSupport i e (e '' ((chart (i : M)) '' C)) = C := by
  have he : e.symm '' (e '' ((chart (i : M)) '' C)) = (chart (i : M)) '' C := by
    ext y
    constructor
    · rintro ⟨z,⟨q,hq,rfl⟩,rfl⟩
      simpa only [e.left_inv (hphase hq)] using hq
    · intro hy
      exact ⟨e y,⟨y,hy,rfl⟩,e.left_inv (hphase hy)⟩
  have hc : (chart (i : M)).symm '' ((chart (i : M)) '' C) = C := by
    ext p
    constructor
    · rintro ⟨q,⟨x,hx,rfl⟩,rfl⟩
      simpa only [(chart (i : M)).left_inv (hchart hx)] using hx
    · intro hp
      exact ⟨chart (i : M) p,⟨p,hp,rfl⟩,(chart (i : M)).left_inv (hchart hp)⟩
  rw [phaseSurfaceSupport,he,hc,hC.closure_eq]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
