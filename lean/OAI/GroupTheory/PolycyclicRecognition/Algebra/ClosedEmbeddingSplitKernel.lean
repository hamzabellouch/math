import OAI.GroupTheory.PolycyclicRecognition.Algebra.QuotientSectionCoordinates
import Mathlib.Topology.Constructions.SumProd

namespace OAI

/-! # A closed kernel embedding gives a closed embedding over a split quotient -/

noncomputable section
namespace PolycyclicRecognition

variable {N G Q : Type*} [Group N] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace G] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup G] [IsTopologicalGroup Q]
  (f : N →* G) (hf : Continuous f) (π : G →* Q) (hπ : Continuous π)
  (s : C(Q, N)) (hs : ∀ q, π (f (s q)) = q)

/-- The homomorphism on the actual kernels. -/
def splitKernelHom : (π.comp f).ker →* π.ker :=
  { toFun n := ⟨f n, n.property⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' a b := Subtype.ext (map_mul f (a : N) (b : N)) }

omit [IsTopologicalGroup Q] in
include hf hπ s hs in
/-- Global section coordinates reduce closedness and the induced topology
of a subgroup to those of its map on the kernel. -/
theorem closedEmbedding_of_splitKernel
    (hk : Topology.IsClosedEmbedding (splitKernelHom f π)) :
    Topology.IsClosedEmbedding f := by
  let sG : C(Q, G) := ⟨fun q => f (s q), hf.comp s.continuous⟩
  let eN := quotientSectionHomeomorph (π.comp f) (hπ.comp hf) s hs
  let eG := quotientSectionHomeomorph π hπ sG hs
  have heq : f = eG.symm ∘ Prod.map id (splitKernelHom f π) ∘ eN := by
    funext n
    change f n = f (n * (s (π (f n)))⁻¹) * f (s (π (f n)))
    rw [map_mul, map_inv, inv_mul_cancel_right]
  rw [heq]
  exact eG.symm.isClosedEmbedding.comp
    ((Topology.IsClosedEmbedding.id.prodMap hk).comp eN.isClosedEmbedding)

end PolycyclicRecognition

end

end OAI
