import OAI.Computability.PerfectCompleteness.Decoding.RepresentativeBucketCollisionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.GoodAdviceEventsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalFrozenTablesLemmas

namespace OAI


namespace PerfectCompleteness.HierarchicalPrediction

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

section Selection

variable {E K Y : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 E]
  [FiniteDimensional F2 K] [Fintype E] [Fintype K] [Fintype Y]

def selectedValue (f : (E →ₗ[F2] K) → Option Y) (r : Nat) (ρ : ℝ)
    (A : ManyGoodRows.RowMap K r) (X : E →ₗ[F2] K) : Option Y :=
  if h : ManyGoodRows.GoodRow f r ρ A (A.comp X) then
    some (ManyGoodRows.selectWitness f r ρ A (A.comp X) h).value
  else none

omit [FiniteDimensional F2 E] [FiniteDimensional F2 K] [Fintype Y] in
theorem selectedValue_of_I (f : (E →ₗ[F2] K) → Option Y) (r : Nat) (ρ : ℝ)
    (A : ManyGoodRows.RowMap K r) (X : E →ₗ[F2] K)
    (hI : GoodAdviceEvents.I f r ρ (A, X) = true) :
    ∃ y, selectedValue f r ρ A X = some y ∧ f X = some y := by
  unfold GoodAdviceEvents.I GoodAdviceEvents.selectedAgreement at hI
  by_cases h : ManyGoodRows.GoodRow f r ρ A (A.comp X)
  · simp only [dite_eq_left h, decide_eq_true_eq] at hI
    exact ⟨(ManyGoodRows.selectWitness f r ρ A (A.comp X) h).value,
      by simp only [selectedValue, dite_eq_left h], hI.2⟩
  · simp only [dite_eq_right h, Bool.false_eq_true] at hI

end Selection

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

abbrev quotientMatrix (X : HierarchicalMatrixTable.Matrix (rows := rows) slots upper) :=
  MatrixRowQuotient.projectMatrix
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background) X

def affinePrediction (X : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (y : Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :
    Block rows upper :=
  X (RepresentativeMatrixTable.correctionFunctional (TreeCanonical.numberedSlots slots)
    (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background)
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap_spec slots upper lowerLevel background) y.2) + y.1

variable (lower : Nodes branch n) (hne : upper ≠ lower) (a : Block rows lower)

def rightUpper (X : HierarchicalMatrixTable.Matrix (rows := rows) slots upper) :
    Block rows upper :=
  (KeyStrategy.response σ .right (TreeCanonical.numberedSlots slots)
    (BlockQuotient.projectBlock lower a ∘
      HierarchicalMatrixTable.displayed slots upper background X)).2.1 ⟨upper, hne⟩

def LowerAccepts (X : HierarchicalMatrixTable.Matrix (rows := rows) slots upper) : Prop :=
  CanonicalEdges.coarsen (TreeCanonical.numberedSlots slots)
    (HierarchicalMatrixTable.displayed slots upper background X)
    (BlockQuotient.projectBlock lower a)
    (KeyStrategy.label σ .left (TreeCanonical.numberedSlots slots)
      (HierarchicalMatrixTable.displayed slots upper background X)) =
    KeyStrategy.label σ .right (TreeCanonical.numberedSlots slots)
      (BlockQuotient.projectBlock lower a ∘
        HierarchicalMatrixTable.displayed slots upper background X)

theorem rightUpper_eq_raw (X : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (hacc : LowerAccepts slots upper background σ lower a X) :
    rightUpper slots upper background σ lower hne a X =
      (CanonicalMatrixTable.response (TreeCanonical.numberedSlots slots)
        (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background)
        σ X).1 := by
  unfold LowerAccepts at hacc
  rw [CanonicalEdges.coarsen_eq_iff] at hacc
  have hcoordinate := congrArg (fun z => z.2.1 ⟨upper, hne⟩) hacc
  have hraw := congrArg Prod.fst
    (HierarchicalMatrixTable.response_eq_split_response slots upper σ background X)
  exact hcoordinate.symm.trans hraw.symm

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)

theorem table_some_iff (X : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (y : Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :
    HierarchicalUsefulness.table slots upper lowerLevel original arrays lowerEvent κ σ background
        (quotientMatrix slots upper lowerLevel background X) = some y ↔
      HierarchicalUsefulness.mark slots upper lowerLevel original arrays lowerEvent κ
        ⟨background, quotientMatrix slots upper lowerLevel background X⟩ = true ∧
      RepresentativeMatrixTable.response (TreeCanonical.numberedSlots slots)
        (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background)
        σ (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (HierarchicalFrozenTables.sectionMap slots upper lowerLevel background) X = y := by
  unfold HierarchicalUsefulness.table HierarchicalFrozenTables.table
    RepresentativeMatrixTable.partialTable RepresentativeMatrixTable.response
    RepresentativeMatrixTable.representative
  split <;> simp_all

theorem I_implies_mark (r : Nat) (ρ : ℝ)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (X : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (hI : GoodAdviceEvents.I
      (HierarchicalUsefulness.table slots upper lowerLevel original arrays lowerEvent κ σ background)
      r ρ (A, quotientMatrix slots upper lowerLevel background X) = true) :
    HierarchicalUsefulness.mark slots upper lowerLevel original arrays lowerEvent κ
      ⟨background, quotientMatrix slots upper lowerLevel background X⟩ = true := by
  obtain ⟨y, _, hy⟩ := selectedValue_of_I _ r ρ A _ hI
  exact ((table_some_iff slots upper lowerLevel background σ original arrays lowerEvent κ X y).mp hy).1

def prediction (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
    (X : HierarchicalMatrixTable.Matrix (rows := rows) slots upper) : Bool :=
  let f := HierarchicalUsefulness.table slots upper lowerLevel original arrays lowerEvent κ σ background
  let Q := quotientMatrix slots upper lowerLevel background X
  GoodAdviceEvents.J f r ρ (A, Q) &&
    match selectedValue f r ρ A Q with
    | none => false
    | some y => decide (rightUpper slots upper background σ lower hne a X =
        affinePrediction slots upper lowerLevel background X y)

theorem lower_accepts_predicts (r : Nat) (ρ : ℝ)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (X : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (hacc : LowerAccepts slots upper background σ lower a X)
    (hI : GoodAdviceEvents.I
      (HierarchicalUsefulness.table slots upper lowerLevel original arrays lowerEvent κ σ background)
      r ρ (A, quotientMatrix slots upper lowerLevel background X) = true) :
    prediction slots upper lowerLevel background σ lower hne a original arrays lowerEvent κ r ρ A X = true := by
  obtain ⟨y, hselected, hy⟩ := selectedValue_of_I _ r ρ A _ hI
  have hmatch := ((table_some_iff slots upper lowerLevel background σ original arrays
    lowerEvent κ X y).mp hy).2
  have hraw := RepresentativeDecoder.raw_selected_output_at_match
    (TreeCanonical.numberedSlots slots) (NodeEmbedding.RowSpace slots upper)
    (HierarchicalMatrixTable.other slots upper background)
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap_spec slots upper lowerLevel background) σ
    (HierarchicalFrozenTables.determined slots upper lowerLevel background) X y hmatch
  have hright : rightUpper slots upper background σ lower hne a X =
      affinePrediction slots upper lowerLevel background X y :=
    (rightUpper_eq_raw slots upper background σ lower hne a X hacc).trans hraw
  have hJ := GoodAdviceEvents.I_implies_J _ r ρ _ hI
  simp only [prediction, hJ, hselected, hright, decide_true, Bool.and_true]

end
end PerfectCompleteness.HierarchicalPrediction

end OAI
