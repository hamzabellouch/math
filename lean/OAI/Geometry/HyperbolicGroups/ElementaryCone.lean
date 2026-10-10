import Mathlib
import OAI.Geometry.HyperbolicGroups.LetterCover

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable

lemma macroCell_representative (c : MacroCell) :
    ∃ e : MacroGraph.graph.Dart, macroCell e = c ∧ macroOrientation e = 1 := by
  have h : ∃ e : MacroGraph.graph.Dart, macroCell e = c := by
    rcases c with ⟨c,hc⟩
    induction c using Sym2.inductionOn with
    | hf a b => exact ⟨⟨(a,b),hc⟩,rfl⟩
  obtain ⟨e,he⟩ := h
  by_cases ho : macroOrientation e = 1
  · exact ⟨e,he,ho⟩
  · refine ⟨e.symm,(macroCell_symm e).trans he,?_⟩
    rw [macroOrientation_symm]
    have hn : macroOrientation e = -1 := by
      have hh : macroOrientation e = 1 ∨ macroOrientation e = -1 := by
        unfold macroOrientation
        split_ifs <;> simp
      exact hh.resolve_left ho
    rw [hn]; norm_num

/-- A canonical positive orientation, with exactly ONE elementary triangle
per unoriented macro edge. No redundant simple-cycle disks are introduced. -/
def macroCellDart (c : MacroCell) : MacroGraph.graph.Dart := (macroCell_representative c).choose
lemma macroCellDart_cell (c : MacroCell) : macroCell (macroCellDart c) = c :=
  (macroCell_representative c).choose_spec.1
lemma macroCellDart_orientation (c : MacroCell) : macroOrientation (macroCellDart c) = 1 :=
  (macroCell_representative c).choose_spec.2

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- The actual pre-compression finite incidence data:
old fan apices, separate top apices, every labelled radial edge, and elementary
triangles. This data is not claimed to be a constructed topological CW space. -/
abbrev ElementaryVertex := Vertex n w ⊕ Top n w
abbrev ElementaryEdge := Edge n w ⊕ (Top n w × MacroGraph.Vertex)
abbrev ElementaryDart := ElementaryEdge n w × Bool
abbrev ElementaryCell := (Top n w × MacroCell) ⊕ FrozenCell n w d

def elementaryOld (e : Dart n w) : ElementaryDart n w := (.inl e.1,e.2)
def elementaryRev (e : ElementaryDart n w) : ElementaryDart n w := (e.1,!e.2)
def elementaryStart : ElementaryDart n w → ElementaryVertex n w
  | (.inl e,b) => .inl (start n w (e,b))
  | (.inr a,true) => .inr a.1
  | (.inr a,false) => .inl (macroVertex n w a.1 a.2)

lemma elementaryRev_rev (e : ElementaryDart n w) :
    elementaryRev n w (elementaryRev n w e) = e := by
  rcases e with ⟨e,b⟩; cases b <;> rfl

lemma elementaryOld_rev (e : Dart n w) :
    elementaryOld n w (rev n w e) = elementaryRev n w (elementaryOld n w e) := rfl

/-- The three literal sides of a top cone triangle, including its two new
radial edges; arbitrary repeated OLD endpoints remain allowed. -/
def elementaryTriangle (a : Top n w) (e : MacroGraph.graph.Dart) : Fin 3 → ElementaryDart n w :=
  ![(.inr (a,e.fst),true), elementaryOld n w (macroStep n w a e.adj), (.inr (a,e.snd),false)]

lemma elementaryTriangle_closed (a : Top n w) (e : MacroGraph.graph.Dart) (i : Fin 3) :
    elementaryStart n w (elementaryTriangle n w a e (finRotate 3 i)) =
      elementaryStart n w (elementaryRev n w (elementaryTriangle n w a e i)) := by
  fin_cases i
  · change Sum.inl (start n w (macroStep n w a e.adj)) = Sum.inl (macroVertex n w a e.fst)
    exact congrArg Sum.inl (macroStep_start n w a e.adj)
  · change Sum.inl (macroVertex n w a e.snd) = Sum.inl (start n w (rev n w (macroStep n w a e.adj)))
    exact congrArg Sum.inl (macroStep_end n w a e.adj).symm
  · rfl

def elementarySize : ElementaryCell n w d → ℕ
  | .inl _ => 3
  | .inr a => (frozenBoundary n w d).size a

def elementarySide : (a : ElementaryCell n w d) → Fin (elementarySize n w d a) → ElementaryDart n w
  | .inl a => elementaryTriangle n w a.1 (macroCellDart a.2)
  | .inr a => fun i => elementaryOld n w ((frozenBoundary n w d).label a i)

/-- Full boundary certificate for the actual elementary two-cells. -/
def elementaryBoundary : PolygonTarget.Boundary (ElementaryCell n w d) (ElementaryDart n w)
    (ElementaryVertex n w) where
  size := elementarySize n w d
  positive := by rintro (a|a); exact Nat.zero_lt_succ _; exact (frozenBoundary n w d).positive a
  label := elementarySide n w d
  start := elementaryStart n w
  rev := elementaryRev n w
  inv := elementaryRev_rev n w
  closed := by
    rintro (a|a) i
    · exact elementaryTriangle_closed n w a.1 (macroCellDart a.2) i
    · exact congrArg Sum.inl ((frozenBoundary n w d).closed a i)

/-- The elementary cells have the SAME independent lift indices as the
integral chain endpoint, not the redundant auxiliary polygon-cell indices. -/
lemma elementaryCell_eq_chain_index :
    ElementaryCell n w d = ((Top n w × MacroCell) ⊕ FrozenCell n w d) := rfl

variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

/-- Extension to the actual top radial edges. Deck coordinates of a top lift
are measured at its apex, so all of its elementary triangles have the same
apex coordinate used by `LiftedCellularChain`. -/
def elementaryVoltage : ElementaryDart n w → G
  | (.inl e,b) => v (e,b)
  | (.inr a,true) => macroPotential n w v a.1 a.2
  | (.inr a,false) => (macroPotential n w v a.1 a.2)⁻¹

include hv in
lemma elementaryVoltage_rev (e : ElementaryDart n w) :
    elementaryVoltage n w v (elementaryRev n w e) = (elementaryVoltage n w v e)⁻¹ := by
  rcases e with ⟨e|a,b⟩
  · exact hv (e,b)
  · cases b <;> simp [elementaryVoltage,elementaryRev]

include hv hcell in
lemma elementaryVoltage_triangle (a : Top n w) (e : MacroGraph.graph.Dart) :
    (List.ofFn (fun i => elementaryVoltage n w v (elementaryTriangle n w a e i))).prod = 1 := by
  have he := macroPotential_edge n w d v hv hcell a e.adj
  simp only [elementaryTriangle,List.ofFn_succ,List.ofFn_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    List.prod_cons,List.prod_nil,elementaryOld,elementaryVoltage,mul_one]
  rw [← mul_assoc,he,mul_inv_cancel]

include hv hcell in
lemma elementaryVoltage_cell (a : ElementaryCell n w d) :
    (List.ofFn (fun i => elementaryVoltage n w v (elementarySide n w d a i))).prod = 1 := by
  rcases a with a|a
  · exact elementaryVoltage_triangle n w d v hv hcell a.1 (macroCellDart a.2)
  · exact hcell (frozenCell n w d a)

/-- Unconditional original-group values on the actual pre-compression cells. -/
lemma elementaryLetterVoltage_cell (a : ElementaryCell n w d) :
    (List.ofFn (fun i => elementaryVoltage n w (letterVoltage n w d)
      (elementarySide n w d a i))).prod = 1 :=
  elementaryVoltage_cell n w d (letterVoltage n w d)
    (letterVoltage_rev n w d) (letterVoltage_cell n w d) a

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
