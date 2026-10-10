import OAI.Combinatorics.Crossing.PolygonalNormalization
import OAI.Combinatorics.Crossing.OrderedAffineSubdivision

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem polygonal_normalization_subdivided {m n : ℕ} (D : AdmissibleDrawing m n) :
    ∃ D' : AdmissibleDrawing m n, crossingCount D' ≤ crossingCount D ∧
      ∀ e, Nonempty (PolygonalParametrization (D'.edge e)) := by
  obtain ⟨D',hpoly,hcount⟩ := polygonal_normalization D
  exact ⟨D',hcount,fun e => (hpoly e).nonempty_polygonalParametrization⟩

theorem PolygonalParametrization.pieces_pos {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) : 0 < P.pieces := by
  by_contra hn
  have hp : P.pieces=0 := by omega
  have hi : (0 : Fin (P.pieces+1))=Fin.last P.pieces := by
    apply Fin.ext
    exact hp.symm
  have he := P.first.symm.trans ((congrArg P.knot hi).trans P.last)
  exact zero_ne_one he

end Zarankiewicz

end

end OAI
