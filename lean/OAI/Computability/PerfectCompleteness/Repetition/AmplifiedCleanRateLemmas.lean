import OAI.Computability.PerfectCompleteness.Reduction.OddListGame
import OAI.Computability.PerfectCompleteness.Repetition.CutChildCleanLawLemmas

namespace OAI

section

namespace PerfectCompleteness.ProjectedCleanRate

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces ProjectedCardinality CleanTreeFactors UniformCleanSources

noncomputable section

section

variable {v m s L cube : Nat} [NeZero m] [NeZero s]
  (clauses : Fin m → SourceClause.NormalizedClause v) (γ : ℚ)
  (hγ : 0 < γ) (hγ1 : γ ≤ 1)
  {R D : Fin (cube ^ 3) → Type*}
  [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
  (branch : Nat → Nat) (height calls : Nat) (rows : Nat → Nat)

variable (ids : (i : Fin (cube ^ 3)) →
  SourceOddLists.Occurrences m (SourceOddLists.repetitionLength γ s hγ hγ1) × R i → Slots branch height → Fin (SourceOddLists.repetitionLength γ s hγ hγ1) → Nat)

local notation "Ωsource" => Factors branch height (SourceOddLists.repetitionLength γ s hγ hγ1) calls rows ids
local notation "zsource" => zeros branch height (SourceOddLists.repetitionLength γ s hγ hγ1) calls rows ids

omit [∀ index, DecidableEq (D index)] in
theorem amplified_source_bound (hcube : 0 < cube)
    (gap : SourceAmplification.ClauseGap clauses γ)
    (hL : 0 < L) (alphabet : SourceOddLists.alphabetLog s (SourceOddLists.repetitionLength γ s hγ hγ1) ≤ L)
    (ν : (i : Fin (cube ^ 3)) → FiniteDistribution (R i))
    (nonprojected : (i : Fin (cube ^ 3)) →
      SourceOddLists.Occurrences m (SourceOddLists.repetitionLength γ s hγ hγ1) × R i → FiniteDistribution (D i))
    (event : UniformCleanSoundness.Sample (D := D) Ωsource → Bool)
    (strategies : (record : UniformCleanSoundness.FullRecord (D := D) Ωsource) →
      Strategy (CleanIndices Ωsource record → Fin (SourceOddLists.repetitionLength γ s hγ hγ1) → Fin m)
        (CleanIndices Ωsource record → Fin (SourceOddLists.repetitionLength γ s hγ hγ1) → Fin v)
        (CleanIndices Ωsource record → OddLists.OddList s (SourceOddLists.LeftLabels (SourceOddLists.repetitionLength γ s hγ hγ1)))
        (CleanIndices Ωsource record → OddLists.OddList s (SourceOddLists.RightLabels (SourceOddLists.repetitionLength γ s hγ hγ1))))
    (inclusion : ∀ record x, recordEvent (D := D) Ωsource zsource record x = true →
      event x = true →
      (IndexedRepetition.game (SourceOddLists.game s clauses (SourceOddLists.repetitionLength γ s hγ hγ1))
        (CleanIndices Ωsource record)).wins (strategies record)
          (fun i => (x i.1).1) = true) :
    (childrenLaw Ωsource (fun _ => SourceOddLists.tupleLaw m (SourceOddLists.repetitionLength γ s hγ hγ1)) ν
      (fun _ => projectionFlag cube hcube) nonprojected).probability event ≤
      (1 - coefficient L branch height (SourceOddLists.repetitionLength γ s hγ hγ1) calls rows / (cube : ℝ) ^ 2) ^ (cube ^ 3) := by
  exact bound_from_repetition branch height (SourceOddLists.repetitionLength γ s hγ hγ1) calls rows ids hcube
    (SourceOddLists.game s clauses (SourceOddLists.repetitionLength γ s hγ hγ1))
    (SourceOddLists.repetition_halfRate clauses γ hγ hγ1 gap hL alphabet)
    ν nonprojected event strategies inclusion

end

end
end PerfectCompleteness.ProjectedCleanRate

end

section

namespace PerfectCompleteness.ProjectedCleanSoundness

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open ProjectedCardinality ProjectedCleanLaw UniformCleanSources UniformCleanSoundness
open OddLists

noncomputable section

attribute [local instance] Classical.propDecidable

variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
  {R J D : I → Type*}
  [∀ i, Fintype (R i)] [∀ i, Fintype (J i)] [∀ i, Fintype (D i)]
  [∀ i, DecidableEq (R i)] [∀ i, DecidableEq (J i)] [∀ i, DecidableEq (D i)]
  (branch : I → Nat → Nat) (t : I → Nat)
  (height : (i : I) → J i → Nat) (square : (i : I) → J i → Bool)
  (ids : (i : I) → (E × R i) → (j : J i) →
    RecursiveSpaces.Slots (branch i) (height i j) → Fin (t i) → Nat)

local notation "Ωtree" => treeFactors branch t height square ids
local notation "ztree" => treeZeros branch t height square ids

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] [DecidableEq A₁] [DecidableEq A₂]
  [Nonempty A₁] [Nonempty A₂]

omit [∀ index, DecidableEq (D index)] in
theorem odd_list_bound {s L : Nat} [NeZero s]
    (μ : FiniteDistribution E) (left : E → Q₁) (right : E → Q₂)
    (projection : E → A₁ → A₂)
    (determined : (OddListGame.base μ left right projection).EndpointDetermined)
    (gap : (s : ℝ) ^ 2 * (OddListGame.base μ left right projection).value ≤ 1 / 2)
    (hL : 0 < L)
    (alphabet : UniqueGamesTheorem.Foundations.Repetition.logTwo
      ((Fintype.card (OddList s A₁) : ℝ) * (Fintype.card (OddList s A₂) : ℝ)) ≤ L)
    (ν : (i : I) → FiniteDistribution (R i))
    (flag : (i : I) → FiniteDistribution Bool)
    (nonprojected : (i : I) → E × R i → FiniteDistribution (D i))
    (event : Sample (D := D) Ωtree → Bool)
    (strategies : (record : FullRecord (D := D) Ωtree) →
      Strategy (CleanIndices Ωtree record → Q₁) (CleanIndices Ωtree record → Q₂)
        (CleanIndices Ωtree record → OddList s A₁)
        (CleanIndices Ωtree record → OddList s A₂))
    (inclusion : ∀ record x, recordEvent (D := D) Ωtree ztree record x = true →
      event x = true →
      (IndexedRepetition.game (OddListGame.game s μ left right projection)
        (CleanIndices Ωtree record)).wins (strategies record)
          (fun i => (x i.1).1) = true) :
    (childrenLaw Ωtree (fun _ => μ) ν flag nonprojected).probability event ≤
      ∏ i : I, (1 - (1 - (RepetitionRate.halfRate L : ℝ)) *
        ((flag i).weight true * ∏ j : J i,
          1 / (shapeCardinality (branch i) (t i) (height i) (square i) j : ℝ))) := by
  apply source_soundness Ωtree (OddListGame.game s μ left right projection)
    ν flag nonprojected ztree
    (fun i => shapeCardinality (branch i) (t i) (height i) (square i)) _
    event (RepetitionRate.halfRate L : ℝ) _ strategies inclusion
  · intro i e j
    exact factor_card_eq (square i j) (ids i e j) (fun _ _ => 0)
  · intro n
    exact OddListGame.repetition_halfRate μ left right projection determined gap hL alphabet n

end
end PerfectCompleteness.ProjectedCleanSoundness

end

end OAI
