import OAI.Combinatorics.Crossing.NoAdjacentNormalization
import OAI.Combinatorics.Crossing.LocallyStraightNormalization

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem polygonal_no_adjacent_locally_straight {m n : ℕ} (D : AdmissibleDrawing m n) :
    ∃ A : AdmissibleDrawing m n, crossingCount A ≤ crossingCount D ∧
      (∀ e, HasFiniteAffineCover (A.edge e)) ∧ NoAdjacentCrossings A ∧ LocallyStraightCrossings A := by
  obtain ⟨B,C,E,v,hvinj,hv,hdet,hnorm,hcount⟩ := exists_no_adjacent_assembled D
  exact ⟨E.assembledAdmissible v hvinj hv hdet,hcount,E.assembledEdge_hasFiniteAffineCover v,
    hnorm,E.assembled_locallyStraightCrossings v hvinj hv hdet⟩

end Zarankiewicz

end

end OAI
