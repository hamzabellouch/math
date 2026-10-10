import Mathlib
import OAI.Computability.VertexCover.Fourier.Folding
import OAI.Computability.VertexCover.Reduction.CloneGap

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                          
section

namespace UniqueGames.Foundations.Hastad.FoldedEquation

open UniqueGames.Reduction.CloneGap
open scoped BigOperators

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

abbrev Address (i₀ : I) (j₀ : J) := HalfCube i₀ ⊕ HalfCube j₀

def storedAssignment {i₀ : I} {j₀ : J}
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool) :
    Address i₀ j₀ → Bool := Sum.elim tableA tableB

def rhsCorrection (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (μ : Cube J) : Bool := f i₀ ^^ f (π j₀) ^^ μ j₀

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem correction_eq (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (g μ : Cube J) :
    (f i₀ ^^ g j₀ ^^ thirdQuery π f g μ j₀) = rhsCorrection π i₀ j₀ f μ := by
  change (f i₀ ^^ g j₀ ^^ (g j₀ ^^ (f (π j₀) ^^ μ j₀))) =
    (f i₀ ^^ f (π j₀) ^^ μ j₀)
  cases f i₀ <;> cases g j₀ <;> cases f (π j₀) <;> cases μ j₀ <;> rfl

def equation (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (g μ : Cube J) : Equation (Address i₀ j₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr (canonicalInput j₀ g)
  third := .inr (canonicalInput j₀ (thirdQuery π f g μ))
  rhs := rhsCorrection π i₀ j₀ f μ

theorem xor_corrections (a b «c» u v w : Bool) :
    ((a ^^ b ^^ «c») == (u ^^ v ^^ w)) =
      !((a ^^ u) ^^ (b ^^ v) ^^ («c» ^^ w)) := by
  cases a <;> cases b <;> cases «c» <;> cases u <;> cases v <;> cases w <;> rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

theorem equation_satisfied (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (equation π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      !(foldedAnswer i₀ tableA f ^^ foldedAnswer j₀ tableB g ^^
        foldedAnswer j₀ tableB (thirdQuery π f g μ)) := by
  change ((tableA (canonicalInput i₀ f) ^^ tableB (canonicalInput j₀ g) ^^
      tableB (canonicalInput j₀ (thirdQuery π f g μ))) == rhsCorrection π i₀ j₀ f μ) = _
  rw [← correction_eq π i₀ j₀ f g μ]
  exact xor_corrections _ _ _ _ _ _

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem equation_satisfied_iff (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (equation π i₀ j₀ f g μ) (storedAssignment tableA tableB) = true ↔
      (foldedAnswer i₀ tableA f ^^ foldedAnswer j₀ tableB g ^^
        foldedAnswer j₀ tableB (thirdQuery π f g μ)) = false := by
  rw [equation_satisfied]
  simp

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem equation_indicator (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    (if satisfied (equation π i₀ j₀ f g μ) (storedAssignment tableA tableB)
      then (1 : ℝ) else 0) =
    (if foldedAnswer i₀ tableA f ^^ foldedAnswer j₀ tableB g ^^
      foldedAnswer j₀ tableB (thirdQuery π f g μ) then 0 else 1) := by
  rw [equation_satisfied]
  cases foldedAnswer i₀ tableA f ^^ foldedAnswer j₀ tableB g ^^
    foldedAnswer j₀ tableB (thirdQuery π f g μ) <;> rfl

theorem satisfied_repeated_right {Name : Type} (e : Equation Name)
    (assignment : Name → Bool) (h : e.second = e.third) :
    satisfied e assignment = (assignment e.first == e.rhs) := by
  unfold satisfied
  rw [← h]
  cases assignment e.first <;> cases assignment e.second <;> cases e.rhs <;> rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem equation_repeated_right (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J)
    (h : canonicalInput j₀ g = canonicalInput j₀ (thirdQuery π f g μ)) :
    satisfied (equation π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      (tableA (canonicalInput i₀ f) == rhsCorrection π i₀ j₀ f μ) := by
  apply satisfied_repeated_right
  exact congrArg Sum.inr h

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem restrict_thirdQuery (valid : J → Bool) (π : J → I)
    (f : Cube I) (g μ : Cube J) :
    restrictQuery valid (thirdQuery π f g μ) =
      thirdQuery (fun j : {j : J // valid j = true} => π j.val) f
        (restrictQuery valid g) (restrictQuery valid μ) := rfl

def conditionedEquation (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (f : Cube I) (g μ : Cube J) : Equation (Address i₀ j₀) :=
  equation (fun j => π j.val) i₀ j₀ f (restrictQuery valid g) (restrictQuery valid μ)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedEquation_rhs (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true}) (f : Cube I) (g μ : Cube J) :
    (conditionedEquation valid π i₀ j₀ f g μ).rhs =
      (f i₀ ^^ f (π j₀.val) ^^ μ j₀.val) := rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedEquation_satisfied (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedEquation valid π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      !(foldedAnswer i₀ tableA f ^^ conditionedFoldedAnswer valid j₀ tableB g ^^
        conditionedFoldedAnswer valid j₀ tableB (thirdQuery π f g μ)) := by
  unfold conditionedEquation
  rw [equation_satisfied]
  simp only [conditionedFoldedAnswer, restrict_thirdQuery]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedEquation_satisfied_iff (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedEquation valid π i₀ j₀ f g μ) (storedAssignment tableA tableB) = true ↔
      (foldedAnswer i₀ tableA f ^^ conditionedFoldedAnswer valid j₀ tableB g ^^
        conditionedFoldedAnswer valid j₀ tableB (thirdQuery π f g μ)) = false := by
  rw [conditionedEquation_satisfied]
  simp

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedEquation_indicator (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    (if satisfied (conditionedEquation valid π i₀ j₀ f g μ) (storedAssignment tableA tableB)
      then (1 : ℝ) else 0) =
    (if foldedAnswer i₀ tableA f ^^ conditionedFoldedAnswer valid j₀ tableB g ^^
      conditionedFoldedAnswer valid j₀ tableB (thirdQuery π f g μ) then 0 else 1) := by
  rw [conditionedEquation_satisfied]
  cases foldedAnswer i₀ tableA f ^^ conditionedFoldedAnswer valid j₀ tableB g ^^
    conditionedFoldedAnswer valid j₀ tableB (thirdQuery π f g μ) <;> rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedEquation_repeated_right (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J)
    (h : canonicalInput j₀ (restrictQuery valid g) =
      canonicalInput j₀ (restrictQuery valid (thirdQuery π f g μ))) :
    satisfied (conditionedEquation valid π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      (tableA (canonicalInput i₀ f) == (f i₀ ^^ f (π j₀.val) ^^ μ j₀.val)) := by
  apply satisfied_repeated_right
  exact congrArg Sum.inr h

noncomputable section

def equationAcceptance (ε : ℝ) (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool) : ℝ :=
  𝔼 f, ∑ μ, noiseWeight ε μ *
    (𝔼 g, if satisfied (equation π i₀ j₀ f g μ) (storedAssignment tableA tableB)
      then (1 : ℝ) else 0)

theorem equationAcceptance_eq (ε : ℝ) (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool) :
    equationAcceptance ε π i₀ j₀ tableA tableB =
      testAcceptance ε π (foldedAnswer i₀ tableA) (foldedAnswer j₀ tableB) := by
  unfold equationAcceptance testAcceptance
  simp_rw [equation_indicator]

def conditionedEquationAcceptance (ε : ℝ) (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool) : ℝ :=
  𝔼 f, ∑ μ, noiseWeight ε μ *
    (𝔼 g, if satisfied (conditionedEquation valid π i₀ j₀ f g μ)
      (storedAssignment tableA tableB) then (1 : ℝ) else 0)

theorem conditionedEquationAcceptance_eq (ε : ℝ) (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool) :
    conditionedEquationAcceptance ε valid π i₀ j₀ tableA tableB =
      testAcceptance ε π (foldedAnswer i₀ tableA)
        (conditionedFoldedAnswer valid j₀ tableB) := by
  unfold conditionedEquationAcceptance testAcceptance
  simp_rw [conditionedEquation_indicator]

end

end UniqueGames.Foundations.Hastad.FoldedEquation
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
