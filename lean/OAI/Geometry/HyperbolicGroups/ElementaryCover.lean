import Mathlib
import OAI.Geometry.HyperbolicGroups.CoverBoundary
import OAI.Geometry.HyperbolicGroups.ElementaryCone

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

/-- Deck offset from the specified basepoint of each literal elementary cell.
For a triangle, that basepoint is its top apex; for a frozen cell it is the
initial vertex of the fixed boundary indexing. -/
def elementaryOffset (a : ElementaryCell n w d) (i : Fin (elementarySize n w d a)) : G :=
  ((List.ofFn (fun j => elementaryVoltage n w v (elementarySide n w d a j))).take i.val).prod

include hv hcell in
lemma elementaryOffset_next (a : ElementaryCell n w d) (i : Fin (elementarySize n w d a)) :
    elementaryOffset n w d v a (finRotate _ i) =
      elementaryOffset n w d v a i * elementaryVoltage n w v (elementarySide n w d a i) :=
  group_prefix_rotate _ (elementaryVoltage_cell n w d v hv hcell a) i

/-- Apex coordinate of a triangle lift is exactly its independent chain index. -/
lemma elementaryOffset_triangle_zero (a : Top n w) (c : MacroCell) :
    elementaryOffset n w d v (.inl (a,c)) (0 : Fin 3) = 1 := rfl

lemma elementaryOffset_triangle_one (a : Top n w) (c : MacroCell) :
    elementaryOffset n w d v (.inl (a,c)) (1 : Fin 3) =
      macroPotential n w v a (macroCellDart c).fst := by
  change ((List.ofFn (fun j : Fin 3 => elementaryVoltage n w v
    (elementaryTriangle n w a (macroCellDart c) j))).take 1).prod = _
  simp [elementaryTriangle,List.ofFn_succ,elementaryVoltage]

include hv hcell in
lemma elementaryOffset_triangle_two (a : Top n w) (c : MacroCell) :
    elementaryOffset n w d v (.inl (a,c)) (2 : Fin 3) =
      macroPotential n w v a (macroCellDart c).snd := by
  have he := macroPotential_edge n w d v hv hcell a (macroCellDart c).adj
  change ((List.ofFn (fun j : Fin 3 => elementaryVoltage n w v
    (elementaryTriangle n w a (macroCellDart c) j))).take 2).prod = _
  simpa [elementaryTriangle,List.ofFn_succ,elementaryVoltage,elementaryOld] using he

/-- Literal elementary boundary incidence in the voltage cover, at every deck
translate, including the wraparound side. No covering-space or CW-realization
assertion is made by this finite incidence construction. -/
def elementaryLiftedBoundary : PolygonTarget.Boundary
    (G × ElementaryCell n w d) (G × ElementaryDart n w) (G × ElementaryVertex n w) where
  size a := elementarySize n w d a.2
  positive a := (elementaryBoundary n w d).positive a.2
  label a i := (a.1 * elementaryOffset n w d v a.2 i, elementarySide n w d a.2 i)
  start e := (e.1, elementaryStart n w e.2)
  rev e := (e.1 * elementaryVoltage n w v e.2, elementaryRev n w e.2)
  inv e := by
    apply Prod.ext
    · simp only [elementaryVoltage_rev n w v hv,mul_inv_cancel_right]
    · exact elementaryRev_rev n w e.2
  closed a i := by
    apply Prod.ext
    · exact (congrArg (a.1 * ·) (elementaryOffset_next n w d v hv hcell a.2 i)).trans
        (mul_assoc _ _ _).symm
    · exact (elementaryBoundary n w d).closed a.2 i

/-- The actual original quotient supplies every triangle and frozen-cell lift;
no relator equations or nonvacuity properties are added as hypotheses. -/
def elementaryLetterLiftedBoundary :=
  elementaryLiftedBoundary n w d (letterVoltage n w d)
    (letterVoltage_rev n w d) (letterVoltage_cell n w d)

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
