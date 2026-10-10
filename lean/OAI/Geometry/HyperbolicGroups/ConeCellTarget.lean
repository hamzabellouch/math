import Mathlib
import OAI.Geometry.HyperbolicGroups.MacroWalk
import OAI.Geometry.HyperbolicGroups.ConeGraph
import OAI.Geometry.HyperbolicGroups.PolygonTarget
import OAI.Geometry.HyperbolicGroups.PresentationDisk

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

abbrev TopPolygon := Top n w × ConeWalks.Circuit MacroGraph.graph
abbrev Square := Σ τ : TwoPath,
  {r : rowSupport (.inr (.inr τ)) → Alphabet n // w ⟨.inr (.inr τ),r⟩ = true}
abbrev Six := {r : Fin 6 → Alphabet n // d r = true}

/-- Only actual positions index rows; this extension is a device for reading
an oriented word and cannot introduce duplicate row occurrences. -/
def extendRow (r : Row) (l : rowSupport r → Alphabet n) : Field → Alphabet n :=
  fun f => if h : f ∈ rowSupport r then l ⟨f,h⟩ else (0,true)

lemma row_extend (r : Row) (l : rowSupport r → Alphabet n) :
    TableModel.row rowSupport (extendRow n r l) r = ⟨r,l⟩ := by
  change (⟨r, fun f => extendRow n r l f.val⟩ : TableModel.Entry (A := Alphabet n) rowSupport) = ⟨r,l⟩
  congr 1
  funext f
  simp [extendRow,f.property]

def squareSide (s : Square n w) : Fin 4 → Dart n w :=
  let l := extendRow n (.inr (.inr s.1)) s.2.val
  ![letterDart n w (stepLetter n l (MasterGraph.first s.1)),
    letterDart n w (stepLetter n l (MasterGraph.second s.1)),
    letterDart n w (l (.inr (s.1,0))),letterDart n w (l (.inr (s.1,1)))]

lemma squareSide_start (s : Square n w) (i : Fin 4) :
    start n w (squareSide n w s i) = .inl () := by
  fin_cases i <;> exact start_letter n w _

lemma squareSide_end (s : Square n w) (i : Fin 4) :
    start n w (rev n w (squareSide n w s i)) = .inl () := by
  fin_cases i <;> exact start_letter n w (inverseLetter n _)

def topSide (a : TopPolygon n w) (i : Fin a.2.2.val.length) : Dart n w :=
  macroStep n w a.1 ((MacroGraph.ofCycle a.2.2.val a.2.2.property).adjacent i)

lemma topSide_closed (a : TopPolygon n w) (i : Fin a.2.2.val.length) :
    start n w (topSide n w a (finRotate _ i)) = start n w (rev n w (topSide n w a i)) := by
  rw [topSide,macroStep_start,topSide,macroStep_end]
  rfl

/-- The three actual kinds of faces AFTER radial top triangles have been
assembled and the closed macro walks split into simple cycles. Such assembly
and its genus preservation are separate obligations, not fields here. -/
abbrev Cell := FanTriangle n w ⊕ (TopPolygon n w ⊕ (Square n w ⊕ Six n d))

def size : Cell n w d → ℕ
  | .inl _ => 3
  | .inr (.inl a) => a.2.2.val.length
  | .inr (.inr (.inl _)) => 4
  | .inr (.inr (.inr _)) => 6

def side : (c : Cell n w d) → Fin (size n w d c) → Dart n w
  | .inl f => fanSide n w f
  | .inr (.inl a) => topSide n w a
  | .inr (.inr (.inl s)) => squareSide n w s
  | .inr (.inr (.inr s)) => fun i => letterDart n w (s.val i)

lemma size_positive (c : Cell n w d) : 0 < size n w d c := by
  rcases c with f | (a | (s | s))
  · change 0 < 3; decide
  · exact lt_of_lt_of_le (by decide : 0 < 3) a.2.2.property.three_le_length
  · change 0 < 4; decide
  · change 0 < 6; decide

lemma size_le (c : Cell n w d) : size n w d c ≤ 15 := by
  rcases c with f | (a | (s | s))
  · change 3 ≤ 15; decide
  · exact MacroGraph.cycle_perimeter a.2.2.val a.2.2.property
  · change 4 ≤ 15; decide
  · change 6 ≤ 15; decide

lemma side_closed (c : Cell n w d) (i : Fin (size n w d c)) :
    start n w (side n w d c (finRotate _ i)) = start n w (rev n w (side n w d c i)) := by
  rcases c with f | (a | (s | s))
  · exact fanSide_closed n w f i
  · exact topSide_closed n w a i
  · exact (squareSide_start n w s _).trans (squareSide_end n w s i).symm
  · exact (start_letter n w _).trans (start_letter n w (inverseLetter n _)).symm

def boundary : PictureSwitch.PolygonTarget.Boundary (Cell n w d) (Dart n w) (Vertex n w) where
  size := size n w d
  positive := size_positive n w d
  label := side n w d
  start := start n w
  rev := rev n w
  inv := rev_rev n w
  closed := side_closed n w d

/-- Fully specified indexed oriented boundaries for actual included rows.
This is a concrete instantiation of normal-picture cancellation, not an
abstract diagram carrying the desired fan bound or isoperimetry. -/
def target {A : Type*} [AddCommGroup A] (weight : Cell n w d → A) :=
  (boundary n w d).target weight (isApex n w) (radial n w)

lemma slot_injective (a : Top n w) : Function.Injective (slot n w a) := by
  intro i j h
  exact congrArg (fun b : Fan n w => b.val.1) h

/-- A simple top polygon visits each actual fan occurrence at most once.
Different point types remain different occurrences even if every letter in
their rows has the same value. -/
lemma top_apex_injective (a : TopPolygon n w) (i j : Fin a.2.2.val.length)
    (b : Fan n w) (hi : start n w (topSide n w a i) = .inr b)
    (hj : start n w (topSide n w a j) = .inr b) : i = j := by
  rw [topSide,macroStep_start] at hi hj
  let P := MacroGraph.ofCycle a.2.2.val a.2.2.property
  apply P.injective
  change macroVertex n w a.1 (P.vertex i) = .inr b at hi
  change macroVertex n w a.1 (P.vertex j) = .inr b at hj
  generalize hx : P.vertex i = x at hi ⊢
  generalize hy : P.vertex j = y at hj ⊢
  rcases x with ((p|l)|⟨⟩) <;> rcases y with ((q|m)|⟨⟩) <;>
    simp only [macroVertex,Sum.inl_ne_inr] at hi hj
  exact congrArg MacroGraph.point (slot_injective n w a.1 (Sum.inr.inj (hi.trans hj.symm)))

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
