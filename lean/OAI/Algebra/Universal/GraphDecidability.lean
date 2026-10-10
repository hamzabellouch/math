import OAI.Algebra.Universal.GraphCriterion
import Mathlib.Data.Fintype.Powerset

namespace OAI

/-!
# Decidability of fixed-size graph witnesses

Connectivity is characterized by containment in every Boolean equivalence relation containing
the marked edges. On a finite carrier this gives an executable decision procedure, and hence
a decision procedure for the existence of a graph witness at each fixed size. The size of a
witness in `HasGraphWitness` is not bounded by these results.
-/

namespace FiniteCongruence

/-- A Boolean relation is closed if it is an equivalence containing every marked edge. -/
def ClosedMarking {Lat Carrier : Type} [LE Lat] (color : Carrier → Carrier → Lat)
    (seeds : Finset (Carrier × Carrier)) (rel : Carrier → Carrier → Bool) : Prop :=
  (∀ point, rel point point = true) ∧
  (∀ left right, rel left right = true → rel right left = true) ∧
  (∀ left middle right, rel left middle = true → rel middle right = true → rel left right = true) ∧
  (∀ left right, Marked color seeds left right → rel left right = true)

/-- Connectivity is the intersection of the Boolean equivalence relations containing all
marked edges. This characterization uses classical logic but allows finite enumeration. -/
theorem connected_iff_closedMarkings {Lat Carrier : Type} [LE Lat]
    (color : Carrier → Carrier → Lat) (seeds : Finset (Carrier × Carrier)) (left right : Carrier) :
    Connected color seeds left right ↔
      ∀ rel : Carrier → Carrier → Bool, ClosedMarking color seeds rel → rel left right = true := by
  constructor
  · intro connected rel closed
    induction connected with
    | rel first second marked => exact closed.2.2.2 first second marked
    | refl point => exact closed.1 point
    | symm first second _ inductionHyp => exact closed.2.1 first second inductionHyp
    | trans first middle last _ _ firstHyp secondHyp =>
      exact closed.2.2.1 first middle last firstHyp secondHyp
  · classical
    intro contained
    let rel : Carrier → Carrier → Bool := fun first second =>
      decide (Connected color seeds first second)
    have closed : ClosedMarking color seeds rel := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro point
        exact decide_eq_true (Relation.EqvGen.refl point)
      · intro first second related
        exact decide_eq_true (Relation.EqvGen.symm first second (of_decide_eq_true related))
      · intro first middle last firstRelated secondRelated
        exact decide_eq_true (Relation.EqvGen.trans first middle last
          (of_decide_eq_true firstRelated) (of_decide_eq_true secondRelated))
      · intro first second marked
        exact decide_eq_true (Relation.EqvGen.rel first second marked)
    exact of_decide_eq_true (contained rel closed)

instance decidableAdmissible {Lat Carrier : Type} [LE Lat] [DecidableLE Lat] [Fintype Carrier]
    (color : Carrier → Carrier → Lat) (placement : Carrier → Carrier) :
    Decidable (Admissible color placement) :=
  inferInstanceAs (Decidable
    (∀ left right, color (placement left) (placement right) ≤ color left right))

instance decidableMarked {Lat Carrier : Type} [LE Lat] [DecidableLE Lat]
    [Fintype Carrier] [DecidableEq Carrier] (color : Carrier → Carrier → Lat)
    (seeds : Finset (Carrier × Carrier)) (left right : Carrier) :
    Decidable (Marked color seeds left right) :=
  inferInstanceAs (Decidable
    (∃ placement : Carrier → Carrier, Admissible color placement ∧
      ∃ edge ∈ seeds, placement edge.1 = left ∧ placement edge.2 = right))

instance decidableClosedMarking {Lat Carrier : Type} [LE Lat] [DecidableLE Lat]
    [Fintype Carrier] [DecidableEq Carrier] (color : Carrier → Carrier → Lat)
    (seeds : Finset (Carrier × Carrier)) (rel : Carrier → Carrier → Bool) :
    Decidable (ClosedMarking color seeds rel) :=
  inferInstanceAs (Decidable
    ((∀ point, rel point point = true) ∧
    (∀ left right, rel left right = true → rel right left = true) ∧
    (∀ left middle right, rel left middle = true → rel middle right = true → rel left right = true) ∧
    (∀ left right, Marked color seeds left right → rel left right = true)))

instance decidableConnected {Lat Carrier : Type} [LE Lat] [DecidableLE Lat]
    [Fintype Carrier] [DecidableEq Carrier] (color : Carrier → Carrier → Lat)
    (seeds : Finset (Carrier × Carrier)) (left right : Carrier) :
    Decidable (Connected color seeds left right) :=
  decidable_of_iff
    (∀ rel : Carrier → Carrier → Bool, ClosedMarking color seeds rel → rel left right = true)
    (connected_iff_closedMarkings color seeds left right).symm

/-- An executable fixed-size test, with no classical choice in its computational content. -/
def graphWitnessDecidable (Lat Carrier : Type) [Fintype Lat] [Lattice Lat] [OrderBot Lat]
    [DecidableEq Lat] [DecidableLE Lat] [Fintype Carrier] [DecidableEq Carrier]
    (color : Carrier → Carrier → Lat) : Decidable (IsGraphWitness color) :=
  inferInstanceAs (Decidable
    ((∀ left right, color left right = color right left) ∧
    (∀ left right, color left right = ⊥ ↔ left = right) ∧
    (∀ left right middle, color left right ≤ color left middle ⊔ color middle right) ∧
    (∀ lower upper : Lat, ¬ lower ≤ upper →
      ∃ left right, color left right ≤ lower ∧ ¬ color left right ≤ upper) ∧
    (∀ seeds : Finset (Carrier × Carrier), seeds.Nonempty → ∀ left right,
      color left right ≤ seeds.sup (fun edge => color edge.1 edge.2) →
        Connected color seeds left right)))

/-- Existence of a colored-graph witness at a fixed candidate size is decidable. -/
def graphSizeDecidable (Lat : Type) [Fintype Lat] [Lattice Lat] [OrderBot Lat]
    [DecidableEq Lat] [DecidableLE Lat] (size : ℕ) :
    Decidable (0 < size ∧ ∃ color : Fin size → Fin size → Lat, IsGraphWitness color) := by
  letI : DecidablePred (fun color : Fin size → Fin size → Lat => IsGraphWitness color) :=
    graphWitnessDecidable Lat (Fin size)
  infer_instance

end FiniteCongruence

end OAI
