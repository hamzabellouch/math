import OAI.Combinatorics.ThinTrees.ExtractionBounds

namespace OAI

section

noncomputable section
open Finset Matrix
open scoped MatrixOrder
namespace StrongThinTree.MultiGraph

theorem extraction : ∃R : ℕ, 4 ≤ R ∧ ∀r : ℕ, R ≤ r →
    ∀(n m : ℕ) (G : MultiGraph n m), 2 ≤ n → G.TreePackable univ r →
    ∃X ∈ G.matrixDomain,
      G.TreePackable (G.thresholdEdges (G.resistance X) (4*resistanceT r)) (extractQ r) := by
  obtain ⟨qH,hqH,hresponse⟩ := simultaneous_response_exists
  obtain ⟨R,hR,hnum⟩ := eventual_extraction_numeric qH
  refine ⟨R,hR,fun r hr n m G hn hp => ?_⟩
  obtain ⟨hq,hqr,hstrict⟩ := hnum r hr
  have ht : 0 < resistanceT r := Real.rpow_pos_of_pos
    (by exact_mod_cast (show 0 < r by omega)) _
  exact G.extraction_from_response_threshold hqH hresponse hn hqr hq hp ht hstrict
end StrongThinTree.MultiGraph

end
end

end OAI
