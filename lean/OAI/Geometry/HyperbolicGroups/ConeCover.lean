import Mathlib
import OAI.Geometry.HyperbolicGroups.ConePresentationGroup
import OAI.Geometry.HyperbolicGroups.LiftedClosedPicture

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

/-- Cell lift coordinate at a frozen side, measured from its indexed first
vertex. Reversing orientation changes the initial point but not the cell lift. -/
def frozenOffset (s : (frozenBoundary n w d).Side) : G :=
  let p := (((List.ofFn ((frozenBoundary n w d).label s.1)).take s.2.2.val).map v).prod
  if s.2.1 then p else p * v ((frozenBoundary n w d).label s.1 s.2.2)

include hv in
lemma frozenOffset_opposite (s : (frozenBoundary n w d).Side) :
    frozenOffset n w d v ((frozenBoundary n w d).opposite s) =
      frozenOffset n w d v s * v ((frozenBoundary n w d).sideLabel s) := by
  rcases s with ⟨a,b,i⟩
  cases b with
  | false =>
    change _ = (_ * v ((frozenBoundary n w d).label a i)) * v (rev n w ((frozenBoundary n w d).label a i))
    rw [hv,mul_inv_cancel_right]
    rfl
  | true => rfl

def coverOffset : WalkStep n w d → G
  | .inl s => macroPotential n w v s.1 s.2.fst
  | .inr s => frozenOffset n w d v s

include hv hcell in
lemma coverOffset_opposite (s : WalkStep n w d) :
    coverOffset n w d v (walkOpposite n w d s) =
      coverOffset n w d v s * v (walkLabel n w d s) := by
  rcases s with ⟨a,e⟩ | s
  · exact (macroPotential_edge n w d v hv hcell a e.adj).symm
  · exact frozenOffset_opposite n w d v hv s

/-- The actual regular covering target, constructed from ordinary group edge
values satisfying the ORIGINAL cell equations. No lifted-chain conclusion is
assumed. In particular it applies to quotient group values, not only to the
bouquet auxiliary group. -/
def actualCellCover : WalkCellCover (indexingTarget n w d) G where
  voltage := v
  voltage_rev := hv
  offset := coverOffset n w d v
  offset_opposite := coverOffset_opposite n w d v hv hcell
  free_back := by
    rintro (⟨a,e⟩ | s) (⟨b,f⟩ | t) hs hk he
    · change Sum.inl (a,e.snd) = (Sum.inl (b,f.snd) : WalkVertex n w) at he
      have hh := Sum.inl.inj he
      exact congrArg (fun p : Top n w × MacroGraph.Vertex => macroPotential n w v p.1 p.2) hh
    · cases hk
    · cases hs
    · cases hs

/-- Canonical cover data for this presentation, with actual prefix-product
coordinates and the proved cone potentials. -/
def polygonGroupCover : WalkCellCover (indexingTarget n w d) (PolygonGroup n w d) :=
  actualCellCover n w d (polygonValue n w d) (polygonValue_rev n w d) (polygonValue_cell n w d)

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
