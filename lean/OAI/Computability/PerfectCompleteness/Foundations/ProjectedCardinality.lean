import OAI.Computability.PerfectCompleteness.Construction.TreeSourceSpaces
import OAI.Computability.PerfectCompleteness.Sampling.UniformLatent

namespace OAI

section

namespace PerfectCompleteness.ProjectedCardinality

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces PointwiseSpaces UniformLatent

variable {branch : Nat → Nat} {n t : Nat}

def projectedSlots (ids : RecursiveSpaces.Slots branch n → Fin t → Nat) :
    RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot :=
  fun s k => MixedSupport.Slot.bit (ids s k)

theorem projected_leaf_domain (ids : RecursiveSpaces.Slots branch n → Fin t → Nat)
    (s : RecursiveSpaces.Slots branch n) :
    LeafDomain (projectedSlots ids) s = (Fin t → Bool) := rfl

def Factor (square : Bool) (ids : RecursiveSpaces.Slots branch n → Fin t → Nat) : Type :=
  if square then squareSpace (H (projectedSlots ids)) else H (projectedSlots ids)

instance factorFinite (square : Bool)
    (ids : RecursiveSpaces.Slots branch n → Fin t → Nat) : Finite (Factor square ids) := by
  cases square <;> dsimp [Factor] <;> infer_instance

noncomputable instance factorFintype (square : Bool)
    (ids : RecursiveSpaces.Slots branch n → Fin t → Nat) : Fintype (Factor square ids) :=
  Fintype.ofFinite _

noncomputable instance factorDecidableEq (square : Bool)
    (ids : RecursiveSpaces.Slots branch n → Fin t → Nat) : DecidableEq (Factor square ids) :=
  Classical.decEq _

def factorZero (square : Bool) (ids : RecursiveSpaces.Slots branch n → Fin t → Nat) :
    Factor square ids := by
  cases square
  · change H (projectedSlots ids)
    exact 0
  · change squareSpace (H (projectedSlots ids))
    exact 0

instance factorNonempty (square : Bool)
    (ids : RecursiveSpaces.Slots branch n → Fin t → Nat) : Nonempty (Factor square ids) :=
  ⟨factorZero square ids⟩

def factorEquiv (square : Bool)
    (ids ids' : RecursiveSpaces.Slots branch n → Fin t → Nat) :
    Factor square ids ≃ Factor square ids' := by
  cases square <;> exact Equiv.refl _

theorem factor_card_eq (square : Bool)
    (ids ids' : RecursiveSpaces.Slots branch n → Fin t → Nat) :
    Fintype.card (Factor square ids) = Fintype.card (Factor square ids') :=
  Fintype.card_congr (factorEquiv square ids ids')

section Sampler

variable {S J D : Type*} [Fintype S] [Fintype J] [DecidableEq J] [Fintype D]
  (branch : Nat → Nat) (t : Nat) (height : J → Nat) (square : J → Bool)

noncomputable def shapeCardinality (j : J) : Nat :=
  Fintype.card (Factor (branch := branch) (n := height j) (t := t) (square j)
    (fun _ _ => 0))

omit [Fintype J] [DecidableEq J] in
theorem shapeCardinality_pos (j : J) : 0 < shapeCardinality branch t height square j :=
  Fintype.card_pos

variable (ids : (s : S) → (j : J) → RecursiveSpaces.Slots branch (height j) → Fin t → Nat)

abbrev Factors (s : S) (j : J) : Type := Factor (square j) (ids s j)

omit [Fintype S] [Fintype J] [DecidableEq J] in
theorem factors_same_cardinality (s : S) (j : J) :
    Fintype.card (Factors branch t height square ids s j) =
      shapeCardinality branch t height square j :=
  factor_card_eq (square j) (ids s j) (fun _ _ => 0)

theorem projected_tree_clean_probability (flag : FiniteDistribution Bool)
    (nonprojected : S → FiniteDistribution D) (s : S) :
    (projectedKernel (Factors branch t height square ids) flag nonprojected s).probability
      (projectedZero (Factors branch t height square ids)
        (fun s j => factorZero (square j) (ids s j))) =
      flag.weight true * (∏ j, 1 / (shapeCardinality branch t height square j : ℝ)) :=
  probability_projectedKernel_zero_constant (Factors branch t height square ids)
    flag nonprojected (fun s j => factorZero (square j) (ids s j))
    (shapeCardinality branch t height square)
    (factors_same_cardinality branch t height square ids) s

omit [DecidableEq J] in
theorem shape_zero_probability_pos :
    0 < (∏ j, 1 / (shapeCardinality branch t height square j : ℝ)) := by
  apply Finset.prod_pos
  intro j _
  exact one_div_pos.mpr (Nat.cast_pos.mpr (shapeCardinality_pos branch t height square j))

end Sampler

end PerfectCompleteness.ProjectedCardinality

end

end OAI
