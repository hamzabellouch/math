import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Incidence.FiniteAffinePlane

namespace OAI

namespace Balanced
open scoped _root_.Balanced

section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def linesInDirectionEquiv (d : Direction F) :
    {l : Line F // l.1 = d} ≃ F where
  toFun l := l.val.2
  invFun b := ⟨(d, b), rfl⟩
  left_inv l := by
    apply Subtype.ext
    apply Prod.ext
    · exact l.property.symm
    · rfl
  right_inv _ := rfl

omit [Field F] in
theorem card_lines_direction (d : Direction F) :
    (Finset.univ.filter (fun l : Line F => l.1 = d)).card = Fintype.card F := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (linesInDirectionEquiv d)

end

noncomputable def coordinatePlane (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    FiniteAffine.Plane (Fintype.card F) (Point F) (Direction F) (Line F) where
  direction := Prod.fst
  incident := OnLine
  card_points := by simp [Point, pow_two]
  card_directions := Fintype.card_option
  card_lines_direction := by
    intro d
    convert (card_lines_direction (F := F) d) using 1
    congr 1
    ext l
    simp
  card_points_line := by
    intro l
    convert (linePoints_card l) using 1
    congr 1
    ext p
    simp [linePoints]
  unique_line_direction := by
    intro p d
    refine ⟨lineThrough d p, ⟨rfl, onLine_lineThrough d p⟩, ?_⟩
    intro l hl
    rw [line_eq_lineThrough p l hl.2, hl.1]
  unique_join := existsUnique_line_of_ne

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[simp] theorem coordinatePlane_direction (l : Line F) :
    (coordinatePlane F).direction l = l.1 := rfl

@[simp] theorem coordinatePlane_incident (p : Point F) (l : Line F) :
    (coordinatePlane F).incident p l ↔ OnLine p l := Iff.rfl

@[simp] theorem coordinatePlane_linePoints (l : Line F) :
    (coordinatePlane F).linePoints l = linePoints l := by
  ext p
  simp only [FiniteAffine.Plane.linePoints, linePoints, Finset.mem_filter,
    Finset.mem_univ, true_and, coordinatePlane_incident]

end Balanced

end OAI
