import Mathlib
import OAI.Combinatorics.IndependentSets.Fourier.FoldedEquation

namespace OAI

namespace IndependentSetsGames.Foundations.Hastad

open IndependentSetsGames.Reduction.CloneGap
open scoped BigOperators

def mapEquation {Name Name' : Type} (rename : Name → Name')
    (e : Equation Name) : Equation Name' where
  first := rename e.first
  second := rename e.second
  third := rename e.third
  rhs := e.rhs

theorem satisfied_mapEquation {Name Name' : Type} (rename : Name → Name')
    (e : Equation Name) (assignment : Name' → Bool) :
    satisfied (mapEquation rename e) assignment = satisfied e (assignment ∘ rename) := rfl

namespace EmptyContext

variable {I : Type}

abbrev Address (i₀ : I) := HalfCube i₀ ⊕ Unit

def storedAssignment {i₀ : I} (table : HalfCube i₀ → Bool) (dummy : Bool) :
    Address i₀ → Bool := Sum.elim table (fun _ => dummy)

def equation (i₀ : I) (f : Cube I) : Equation (Address i₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr ()
  third := .inr ()
  rhs := f i₀

@[simp] theorem equation_second_eq_third (i₀ : I) (f : Cube I) :
    (equation i₀ f).second = (equation i₀ f).third := rfl

theorem equation_satisfied (i₀ : I) (assignment : Address i₀ → Bool) (f : Cube I) :
    satisfied (equation i₀ f) assignment =
      !(foldedAnswer i₀ (fun h => assignment (.inl h)) f) := by
  rw [FoldedEquation.satisfied_repeated_right (equation i₀ f) assignment rfl]
  change (assignment (.inl (canonicalInput i₀ f)) == f i₀) =
    !(assignment (.inl (canonicalInput i₀ f)) ^^ f i₀)
  cases assignment (.inl (canonicalInput i₀ f)) <;> cases f i₀ <;> rfl

theorem equation_storedAssignment_satisfied (i₀ : I) (table : HalfCube i₀ → Bool)
    (dummy : Bool) (f : Cube I) :
    satisfied (equation i₀ f) (storedAssignment table dummy) =
      !(foldedAnswer i₀ table f) := equation_satisfied i₀ _ f

theorem equation_flip_first (i₀ : I) (f : Cube I) :
    (equation i₀ (cubeFlip f)).first = (equation i₀ f).first := by
  change Sum.inl (canonicalInput i₀ (cubeFlip f)) = Sum.inl (canonicalInput i₀ f)
  rw [canonicalInput_flip]

theorem equation_flip_rhs (i₀ : I) (f : Cube I) :
    (equation i₀ (cubeFlip f)).rhs = !(equation i₀ f).rhs := rfl

theorem equation_satisfied_flip (i₀ : I) (assignment : Address i₀ → Bool)
    (f : Cube I) :
    satisfied (equation i₀ (cubeFlip f)) assignment =
      !(satisfied (equation i₀ f) assignment) := by
  rw [equation_satisfied, foldedAnswer_flip, equation_satisfied]

def pairedEquations (i₀ : I) (f : Cube I) : List (Equation (Address i₀)) :=
  [equation i₀ f, equation i₀ (cubeFlip f)]

@[simp] theorem pairedEquations_length (i₀ : I) (f : Cube I) :
    (pairedEquations i₀ f).length = 2 := rfl

theorem pairedEquations_ne_nil (i₀ : I) (f : Cube I) :
    pairedEquations i₀ f ≠ [] := by simp [pairedEquations]

theorem pairedEquations_acceptedCount (i₀ : I) (assignment : Address i₀ → Bool)
    (f : Cube I) :
    (pairedEquations i₀ f).countP (fun e => satisfied e assignment) = 1 := by
  simp only [pairedEquations, List.countP_cons, List.countP_nil, equation_satisfied_flip]
  cases satisfied (equation i₀ f) assignment <;> rfl

theorem pairedEquations_failureCount (i₀ : I) (assignment : Address i₀ → Bool)
    (f : Cube I) :
    (pairedEquations i₀ f).countP (fun e => !(satisfied e assignment)) = 1 := by
  simp only [pairedEquations, List.countP_cons, List.countP_nil, equation_satisfied_flip]
  cases satisfied (equation i₀ f) assignment <;> rfl

noncomputable section

variable [Fintype I] [DecidableEq I]

def equationAcceptance (i₀ : I) (assignment : Address i₀ → Bool) : ℝ :=
  𝔼 f : Cube I, if satisfied (equation i₀ f) assignment then (1 : ℝ) else 0

def equationBias (i₀ : I) (assignment : Address i₀ → Bool) : ℝ :=
  𝔼 f : Cube I, if satisfied (equation i₀ f) assignment then (1 : ℝ) else -1

theorem foldedMean_eq_zero (i₀ : I) (table : HalfCube i₀ → Bool) :
    (𝔼 f : Cube I, bitSign (foldedAnswer i₀ table f)) = 0 := by
  simpa [coefficient, walsh, bitSign] using foldedAnswer_zero_coefficient i₀ table

omit [Fintype I] [DecidableEq I] in
theorem equation_indicator (i₀ : I) (assignment : Address i₀ → Bool) (f : Cube I) :
    (if satisfied (equation i₀ f) assignment then (1 : ℝ) else 0) =
      (1 + bitSign (foldedAnswer i₀ (fun h => assignment (.inl h)) f)) / 2 := by
  rw [equation_satisfied]
  cases foldedAnswer i₀ (fun h => assignment (.inl h)) f <;> norm_num [bitSign]

theorem equationAcceptance_eq_half (i₀ : I) (assignment : Address i₀ → Bool) :
    equationAcceptance i₀ assignment = 1 / 2 := by
  unfold equationAcceptance
  simp_rw [equation_indicator, div_eq_mul_inv, ← Finset.expect_mul,
    Finset.expect_add_distrib, Fintype.expect_const, foldedMean_eq_zero]
  norm_num

theorem equationBias_eq_zero (i₀ : I) (assignment : Address i₀ → Bool) :
    equationBias i₀ assignment = 0 := by
  unfold equationBias
  have hi (f : Cube I) :
      (if satisfied (equation i₀ f) assignment then (1 : ℝ) else -1) =
        bitSign (foldedAnswer i₀ (fun h => assignment (.inl h)) f) := by
    rw [equation_satisfied]
    cases foldedAnswer i₀ (fun h => assignment (.inl h)) f <;> norm_num [bitSign]
  simp_rw [hi]
  exact foldedMean_eq_zero i₀ _

theorem mapped_equationAcceptance_eq_half {Name : Type} (i₀ : I)
    (rename : Address i₀ → Name) (assignment : Name → Bool) :
    (𝔼 f : Cube I, if satisfied (mapEquation rename (equation i₀ f)) assignment
      then (1 : ℝ) else 0) = 1 / 2 := by
  simp only [satisfied_mapEquation]
  exact equationAcceptance_eq_half i₀ (assignment ∘ rename)

end
end EmptyContext
end IndependentSetsGames.Foundations.Hastad

end OAI
