import OAI.Computability.PerfectCompleteness.Decoding.CleanLeftDecoderLemmas
import OAI.Computability.PerfectCompleteness.Decoding.DependentDecoderSampling
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalFrozenTablesLemmas

namespace OAI

section

namespace PerfectCompleteness.CleanDecoderSeedLaw

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays CleanDecoderContext
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (E : Exposed branch rows repeats n h t v m upper d)

abbrev LeftAnswer (own : LeftOwn E) :=
  CleanLeftDecoder.UpperAnswer (leftExposed E) upper own

abbrev RightAnswer (own : RightOwn E) :=
  CleanRightDecoder.Answer E.clauses E.designated E.clean E.visible E.projected
    upper (lower E) E.cut (lowerHeight upper d) E.outside own

local instance leftOwnFintype : Fintype (LeftOwn E) :=
  CleanLeftDecoder.ownFintype (leftExposed E)

local instance rightOwnFintype : Fintype (RightOwn E) :=
  inferInstanceAs (Fintype ({i : Fin (branch h) // E.clean i} → Fin t → Fin v))

local instance leftAnswerFintype (own : LeftOwn E) : Fintype (LeftAnswer E own) :=
  CleanLeftDecoder.upperAnswerFintype (leftExposed E) upper own

local instance rightAnswerFintype (own : RightOwn E) : Fintype (RightAnswer E own) :=
  RightDecoder.scalarFintype (rightSlots E own) upper

abbrev Seed := LeftSeed E × RightSeed E

instance seedFintype : Fintype (Seed E) :=
  inferInstanceAs (Fintype
    (((own : LeftOwn E) → LeftAnswer E own) ×
      ((own : RightOwn E) → RightAnswer E own)))

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : CleanLeftDecoder.Useful (leftExposed E) upper (h + 1))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
  (a : OwnInputReference.LowerVector rows (lower E)) (threshold : ℝ)

def leftKernel (own : LeftOwn E) : FiniteDistribution (LeftAnswer E own) :=
  CleanLeftDecoder.law (leftExposed E) upper (h + 1) σ useful r ρ A own

def rightKernel (own : RightOwn E) : FiniteDistribution (RightAnswer E own) :=
  CleanRightDecoder.kernel E.clauses E.designated E.clean E.visible E.projected
    upper (lower E) E.cut (lowerHeight upper d) E.outside
    rows repeats E.rightTape W a σ threshold own

def leftSeedLaw : FiniteDistribution (LeftSeed E) :=
  CleanLeftDecoder.seedLaw (leftExposed E) upper (h + 1) σ useful r ρ A

def rightSeedLaw : FiniteDistribution (RightSeed E) :=
  CleanRightDecoder.seedLaw E.clauses E.designated E.clean E.visible E.projected
    upper (lower E) E.cut (lowerHeight upper d) E.outside
    rows repeats E.rightTape W a σ threshold

def seedLaw : FiniteDistribution (Seed E) :=
  (leftSeedLaw E σ useful r ρ A).product (rightSeedLaw E σ W a threshold)

theorem seedLaw_eq_dependent :
    seedLaw E σ useful r ρ A W a threshold =
      DependentDecoderSampling.seedLaw
        (leftKernel E σ useful r ρ A) (rightKernel E σ W a threshold) := rfl

theorem read_law (left : LeftOwn E) (right : RightOwn E) :
    (seedLaw E σ useful r ρ A W a threshold).pushforward
        (fun seed => (seed.1 left, seed.2 right)) =
      (leftKernel E σ useful r ρ A left).product
        (rightKernel E σ W a threshold right) :=
  DependentDecoderSampling.read_law
    (leftKernel E σ useful r ρ A) (rightKernel E σ W a threshold) left right

theorem probability_read (left : LeftOwn E) (right : RightOwn E)
    (event : LeftAnswer E left → RightAnswer E right → Bool) :
    (seedLaw E σ useful r ρ A W a threshold).probability
        (fun seed => event (seed.1 left) (seed.2 right)) =
      ((leftKernel E σ useful r ρ A left).product
        (rightKernel E σ W a threshold right)).probability
          (fun answer => event answer.1 answer.2) := by
  have hread := FiniteDistribution.probability_pushforward
    (seedLaw E σ useful r ρ A W a threshold)
    (fun seed : Seed E => (seed.1 left, seed.2 right))
    (fun answer => event answer.1 answer.2)
  rw [read_law] at hread
  exact hread.symm

theorem supported_left (seed : Seed E)
    (hs : (seedLaw E σ useful r ρ A W a threshold).weight seed ≠ 0) :
    (leftSeedLaw E σ useful r ρ A).weight seed.1 ≠ 0 := by
  intro hz
  apply hs
  change (leftSeedLaw E σ useful r ρ A).weight seed.1 *
    (rightSeedLaw E σ W a threshold).weight seed.2 = 0
  rw [hz, zero_mul]

theorem supported_right (seed : Seed E)
    (hs : (seedLaw E σ useful r ρ A W a threshold).weight seed ≠ 0) :
    (rightSeedLaw E σ W a threshold).weight seed.2 ≠ 0 := by
  intro hz
  apply hs
  change (leftSeedLaw E σ useful r ρ A).weight seed.1 *
    (rightSeedLaw E σ W a threshold).weight seed.2 = 0
  rw [hz, mul_zero]

theorem supported_left_row (seed : Seed E)
    (hs : (seedLaw E σ useful r ρ A W a threshold).weight seed ≠ 0)
    (own : LeftOwn E) :
    (leftKernel E σ useful r ρ A own).weight (seed.1 own) ≠ 0 :=
  CleanLeftDecoder.supported_row (leftExposed E) upper (h + 1) σ useful r ρ A
    seed.1 (supported_left E σ useful r ρ A W a threshold seed hs) own

theorem supported_right_row (seed : Seed E)
    (hs : (seedLaw E σ useful r ρ A W a threshold).weight seed ≠ 0)
    (own : RightOwn E) :
    (rightKernel E σ W a threshold own).weight (seed.2 own) ≠ 0 :=
  DependentDecoderSampling.supported_right
    (leftKernel E σ useful r ρ A) (rightKernel E σ W a threshold) seed hs own

variable (hbranch : ∀ k < n, 0 < branch k)

theorem supported_output_normalized (hρ : 0 < ρ) (seed : Seed E)
    (hs : (seedLaw E σ useful r ρ A W a threshold).weight seed ≠ 0)
    (own : LeftOwn E) :
    leftOutput E hbranch seed.1 own
      (HierarchicalLeftDecoder.lowerOne (leftSlots E own) upper (h + 1) hbranch d) = 1 :=
  CleanLeftDecoder.supported_output_normalized (leftExposed E) upper (h + 1) σ useful
    hbranch r ρ hρ A seed.1
    (supported_left E σ useful r ρ A W a threshold seed hs) d own

theorem supported_form_tested_rank (hρ : 0 < ρ) (seed : Seed E)
    (hs : (seedLaw E σ useful r ρ A W a threshold).weight seed ≠ 0)
    (own : LeftOwn E) :
    (LowerAffineSliceRank.testedGram
      (FunctionSpaceLowerRank.matrixForm
        (CleanLeftDecoder.LowerH (leftExposed E) upper (h + 1) d own)
        (leftForm E hbranch seed.1 own))
      (HierarchicalLeftDecoder.testedMatrix (leftSlots E own) upper (h + 1)
        (CleanLeftDecoder.background (leftExposed E) upper own) d)).rank ≤ 1 :=
  CleanLeftDecoder.supported_form_tested_rank (leftExposed E) upper (h + 1) σ useful
    hbranch r ρ hρ A seed.1
    (supported_left E σ useful r ρ A W a threshold seed hs) d own

end
end PerfectCompleteness.CleanDecoderSeedLaw

end

section

namespace PerfectCompleteness.OriginalDecoderMark

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev SlotFamily (branch : Nat → Nat) (n t : Nat) :=
  RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot

structure Family (branch rows : Nat → Nat) (n t : Nat)
    (Sample : SlotFamily branch n t → Type*) [∀ slots, Fintype (Sample slots)] where
  original : (slots : SlotFamily branch n t) → FiniteDistribution (Sample slots)
  arrays : (slots : SlotFamily branch n t) → Sample slots → Arrays slots rows
  lowerEvent : (slots : SlotFamily branch n t) → Sample slots → Bool

variable {branch rows : Nat → Nat} {n t : Nat}
  {Sample : SlotFamily branch n t → Type*} [∀ slots, Fintype (Sample slots)]
  (F : Family branch rows n t Sample) (upper : Nodes branch n) (lowerLevel : Nat) (κ : ℝ)

def mark (slots : SlotFamily branch n t)
    (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
    (X : HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background) : Prop :=
  HierarchicalUsefulness.mark slots upper lowerLevel
    (F.original slots) (F.arrays slots) (F.lowerEvent slots) κ ⟨background, X⟩ = true

theorem mark_heq {slots₁ slots₂ : SlotFamily branch n t} (hs : slots₁ = slots₂)
    {background₁ : HierarchicalMatrixTable.Background (rows := rows) slots₁ upper}
    {background₂ : HierarchicalMatrixTable.Background (rows := rows) slots₂ upper}
    (hb : HEq background₁ background₂) :
    HEq (mark F upper lowerLevel κ slots₁ background₁)
      (mark F upper lowerLevel κ slots₂ background₂) := by
  cases hs
  have hb' : background₁ = background₂ := eq_of_heq hb
  cases hb'
  rfl

theorem mark_congr {slots₁ slots₂ : SlotFamily branch n t} (hs : slots₁ = slots₂)
    {background₁ : HierarchicalMatrixTable.Background (rows := rows) slots₁ upper}
    {background₂ : HierarchicalMatrixTable.Background (rows := rows) slots₂ upper}
    (hb : HEq background₁ background₂)
    {X₁ : HierarchicalFrozenTables.QuotientMatrix slots₁ upper lowerLevel background₁}
    {X₂ : HierarchicalFrozenTables.QuotientMatrix slots₂ upper lowerLevel background₂}
    (hX : HEq X₁ X₂) :
    mark F upper lowerLevel κ slots₁ background₁ X₁ ↔
      mark F upper lowerLevel κ slots₂ background₂ X₂ := by
  cases hs
  have hb' : background₁ = background₂ := eq_of_heq hb
  cases hb'
  have hX' : X₁ = X₂ := eq_of_heq hX
  cases hX'
  rfl

theorem table_eq_original (slots : SlotFamily branch n t)
    (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) :
    HierarchicalFrozenTables.table slots upper lowerLevel background σ
        (mark F upper lowerLevel κ slots background) =
      HierarchicalUsefulness.table slots upper lowerLevel (F.original slots)
        (F.arrays slots) (F.lowerEvent slots) κ σ background := rfl

variable {repeats : Nat → Nat} {h v m : Nat} [NeZero m]

def useful (E : CleanLeftDecoder.Exposed branch rows repeats n h t v m) :
    CleanLeftDecoder.Useful E upper lowerLevel :=
  fun own X => mark F upper lowerLevel κ
    (CleanLeftDecoder.slots E own) (CleanLeftDecoder.background E upper own) X

theorem useful_heq
    (E₁ E₂ : CleanLeftDecoder.Exposed branch rows repeats n h t v m)
    (own₁ : CleanLeftDecoder.Own E₁) (own₂ : CleanLeftDecoder.Own E₂)
    (hs : CleanLeftDecoder.slots E₁ own₁ = CleanLeftDecoder.slots E₂ own₂)
    (hb : HEq (CleanLeftDecoder.background E₁ upper own₁)
      (CleanLeftDecoder.background E₂ upper own₂)) :
    HEq (useful F upper lowerLevel κ E₁ own₁) (useful F upper lowerLevel κ E₂ own₂) :=
  mark_heq F upper lowerLevel κ hs hb

theorem useful_at_quotientMatrix
    (E : CleanLeftDecoder.Exposed branch rows repeats n h t v m)
    (own : CleanLeftDecoder.Own E) :
    useful F upper lowerLevel κ E own (CleanLeftDecoder.quotientMatrix E upper lowerLevel own) ↔
      HierarchicalUsefulness.mark (CleanLeftDecoder.slots E own) upper lowerLevel
        (F.original (CleanLeftDecoder.slots E own)) (F.arrays (CleanLeftDecoder.slots E own))
        (F.lowerEvent (CleanLeftDecoder.slots E own)) κ
        (HierarchicalUsefulness.observe (CleanLeftDecoder.slots E own) upper lowerLevel
          (CleanLeftDecoder.arrays E own)) = true := Iff.rfl

theorem law_eq_adviceLaw
    (E : CleanLeftDecoder.Exposed branch rows repeats n h t v m)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
    (own : CleanLeftDecoder.Own E) :
    CleanLeftDecoder.law E upper lowerLevel σ (useful F upper lowerLevel κ E) r ρ A own =
      HierarchicalLeftDecoder.adviceLaw (CleanLeftDecoder.slots E own) upper lowerLevel
        (CleanLeftDecoder.background E upper own) σ
        (mark F upper lowerLevel κ (CleanLeftDecoder.slots E own)
          (CleanLeftDecoder.background E upper own)) r ρ A
        (A.comp (CleanLeftDecoder.quotientMatrix E upper lowerLevel own)) := rfl

end
end PerfectCompleteness.OriginalDecoderMark

end

end OAI
