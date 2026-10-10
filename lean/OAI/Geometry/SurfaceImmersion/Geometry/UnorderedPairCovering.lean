import OAI.Geometry.SurfaceImmersion.Atlas.UnorderedPairChart
import Mathlib.Topology.Homotopy.Lifting

namespace OAI

/-! The unordered-pair quotient is a two-sheeted covering away from
the diagonal. At a diagonal point its fiber is a singleton. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*}

def unorderedDistinctPairs (M : Type*) : Set (UnorderedSurfacePairs M) :=
  {z | ¬ ∃ p : M, unorderedPair (p,p) = z}

lemma unorderedPair_diagonal_iff (z : M × M) (p : M) :
    unorderedPair z = unorderedPair (p,p) ↔ z = (p,p) := by
  rw [unorderedPair_eq]
  simp only [Prod.swap_prod_mk,or_self]

lemma unorderedPair_mem_distinct_iff (z : M × M) :
    unorderedPair z ∈ unorderedDistinctPairs M ↔ z.1 ≠ z.2 := by
  constructor
  · intro hz he
    exact hz ⟨z.1,by rw [show (z.1,z.1) = z from Prod.ext rfl he]⟩
  · intro hz ⟨p,hp⟩
    have he := (unorderedPair_diagonal_iff z p).mp hp.symm
    exact hz (by rw [he])

variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
theorem unorderedPair_covering :
    IsCoveringMapOn (unorderedPair : M × M → UnorderedSurfacePairs M) (unorderedDistinctPairs M) := by
  apply IsCoveringMapOn.of_isLocalHomeomorphOn unorderedPair_continuous
  intro z hz
  have hne : z.1 ≠ z.2 := (unorderedPair_mem_distinct_iff z).mp hz
  obtain ⟨e,he,heq,_⟩ := unordered_pair_local_chart z.1 z.2 hne
  exact ⟨e,he,funext fun z => (heq z).symm⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
