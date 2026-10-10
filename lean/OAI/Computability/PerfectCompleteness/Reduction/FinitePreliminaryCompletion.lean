import OAI.Computability.PerfectCompleteness.Construction.CanonicalLocalCompletion
import OAI.Computability.PerfectCompleteness.Construction.FlexibleLocalCompletionLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedQueryCodec

namespace OAI

section

namespace PerfectCompleteness.FinitePreliminaryCompletion

open MixedSupport CanonicalKeys CanonicalEdges CanonicalLabelEncoding
open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness CompletionSoundness.LegalProjectionGame
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {rows repeats : Nat → Nat}

abbrev alphabet (branch : Nat → Nat) (n t : Nat) (δ : ℚ) : Nat :=
  CanonicalLocalCompletion.alphabet (TreeCanonical.locationCount branch n t) δ

def finiteInput (δ : ℚ) (data : MetadataFreeTape.Input branch n t rows repeats) :
    LocalCompletionFamily.Input (alphabet branch n t δ) :=
  CanonicalPartialTable.lookup
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)
    (CanonicalLocalCompletion.partitionWidth_le_alphabet
      (TreeCanonical.locationCount branch n t) δ)
    (FixedQueryCodec.partialInput data)

def finiteResult (δ : ℚ) (data : MetadataFreeTape.Input branch n t rows repeats) :
    LocalCompletionFamily.Result (alphabet branch n t δ) :=
  LocalCompletionFamily.lookup
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)
    (finiteInput δ data)

theorem finiteResult_correct (δ : ℚ)
    (data : MetadataFreeTape.Input branch n t rows repeats) :
    LocalCompletionFamily.Correct (finiteInput δ data) (finiteResult δ data) :=
  LocalCompletionFamily.lookup_correct
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)
    (finiteInput δ data)
    (FixedQueryCodec.partialInput_admissible
      (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)
      (CanonicalLocalCompletion.partitionWidth_le_alphabet
        (TreeCanonical.locationCount branch n t) δ) data)

abbrev blockFamily (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :=
  HierarchicalGame.toBlockFamily
    (PreliminarySampler.family clauses branch n t rows repeats)

variable (clauses : Fin m → SourceClause.NormalizedClause v)

local notation "F" => blockFamily clauses branch n t rows repeats

def rawInput (δ : ℚ) (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    LocalCompletionFamily.Input (alphabet branch n t δ) :=
  finiteInput δ (MetadataFreeTape.encodeRaw clauses rows repeats e)

theorem rawInput_mask (δ : ℚ)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (rawInput clauses δ e).1 = paddedMask (CanonicalGame.leftKey F e) := by
  unfold rawInput finiteInput
  rw [FixedQueryCodec.partialInput_encodeRaw, CanonicalPartialTable.lookup_mask_actual,
    FixedQueryCodec.leftTable_key]
  rfl

theorem rawInput_image_legal (δ : ℚ)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats)
    (P : CanonicalGame.LeftLabel F (CanonicalGame.leftAt F e)) :
    (rawInput clauses δ e).2
        (CanonicalLocalCompletion.legalL F δ (CanonicalGame.leftAt F e) P) =
      CanonicalLocalCompletion.legalR F δ (CanonicalGame.rightAt F e)
        (CanonicalGame.edge F e P) := by
  let slots := MetadataFreeSampler.sourceSlots clauses e.1.1
  let arrays := WholeArraySampler.evaluate rows repeats
    (GeometricPath.leafPath e.1.2) slots e.2.1
  let S := TreeCanonical.numberedSlots slots
  let f := TreeCanonical.numberedFunction slots (HierarchicalArrays.fullJoint arrays)
  let θ := FixedQueryCodec.rawTestIndex clauses e
  let Pencoded : Label S (FixedQueryCodec.leftEncode branch n rows ∘ f) :=
    CanonicalCoarseningEncoding.transportFine S f
      (FixedQueryCodec.leftEncode branch n rows)
      (FixedQueryCodec.leftEncode_injective branch n rows) P
  have hfinite := CanonicalPartialTable.image_actual_legal
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)
    (CanonicalLocalCompletion.partitionWidth_le_alphabet
      (TreeCanonical.locationCount branch n t) δ)
    S (FixedQueryCodec.leftTable arrays) (FixedQueryCodec.outputMap θ) Pencoded
  have hcoarse := CanonicalCoarseningEncoding.labelEmbedding_coarsen .right
    (CanonicalLocalCompletion.partitionWidth_le_alphabet
      (TreeCanonical.locationCount branch n t) δ)
    S f (FixedQueryCodec.project θ) (FixedQueryCodec.leftEncode branch n rows)
    (FixedQueryCodec.rightEncode θ) (FixedQueryCodec.outputMap θ)
    (FixedQueryCodec.leftEncode_injective branch n rows)
    (FixedQueryCodec.rightEncode_injective θ) (FixedQueryCodec.outputMap_leftEncode θ) P
  unfold rawInput finiteInput
  rw [FixedQueryCodec.partialInput_encodeRaw]
  exact hfinite.trans hcoarse.symm

local instance leftVertex_fintype : Fintype (CanonicalGame.LeftVertex F) :=
  Fintype.ofFinite _

local instance rightVertex_fintype : Fintype (CanonicalGame.RightVertex F) :=
  Fintype.ofFinite _

local instance leftLabel_fintype (x : CanonicalGame.LeftVertex F) :
    Fintype (CanonicalGame.LeftLabel F x) := Fintype.ofFinite _

local instance rightLabel_fintype (y : CanonicalGame.RightVertex F) :
    Fintype (CanonicalGame.RightLabel F y) := Fintype.ofFinite _

local instance rightAlphabet_nonempty (δ : ℚ) : Nonempty (Fin (alphabet branch n t δ)) :=
  ⟨⟨0, CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ⟩⟩

local instance leftAlphabet_nonempty (δ : ℚ) : Nonempty (Fin (2 * alphabet branch n t δ)) :=
  ⟨⟨0, Nat.mul_pos (by decide)
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)⟩⟩

theorem compatible (μ : FiniteDistribution (PreliminarySampler.Raw clauses branch n t rows repeats))
    (δ : ℚ) :
    FlexibleLocalCompletion.Compatible (CanonicalGame.game F μ)
      (CanonicalLocalCompletion.legalL F δ) (CanonicalLocalCompletion.legalR F δ)
      (rawInput clauses δ) where
  mask e a := by
    rw [rawInput_mask]
    exact paddedMask_eq_true_iff (CanonicalGame.leftKey F e)
      (CanonicalLocalCompletion.partitionWidth_le_leftAlphabet
        (TreeCanonical.locationCount branch n t) δ) a
  image e P := rawInput_image_legal clauses δ e P

def family (μ : FiniteDistribution (PreliminarySampler.Raw clauses branch n t rows repeats))
    (δ : ℚ) :
    (CanonicalGame.game F μ).CompletionFamily
      (CanonicalLocalCompletion.legalL F δ) (CanonicalLocalCompletion.legalR F δ) :=
  FlexibleLocalCompletion.family (CanonicalGame.game F μ)
    (CanonicalLocalCompletion.legalL F δ) (CanonicalLocalCompletion.legalR F δ)
    (rawInput clauses δ) (compatible clauses μ δ)
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)
    (by
      intro e b
      rw [Fintype.card_eq_nat_card]
      have h := CanonicalLocalCompletion.small F μ e b
      rw [Fintype.card_eq_nat_card] at h
      exact h)

@[simp] theorem family_size
    (μ : FiniteDistribution (PreliminarySampler.Raw clauses branch n t rows repeats))
    (δ : ℚ) (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (family clauses μ δ).size e = LocalCompletionFamily.activeCount
      (finiteResult δ (MetadataFreeTape.encodeRaw clauses rows repeats e)) := rfl

@[simp] theorem family_map
    (μ : FiniteDistribution (PreliminarySampler.Raw clauses branch n t rows repeats))
    (δ : ℚ) (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (family clauses μ δ).map e = LocalCompletionFamily.table
      (finiteResult δ (MetadataFreeTape.encodeRaw clauses rows repeats e)) := rfl

theorem family_size_le
    (μ : FiniteDistribution (PreliminarySampler.Raw clauses branch n t rows repeats))
    (δ : ℚ) (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (family clauses μ δ).size e ≤ 2 * alphabet branch n t δ :=
  LocalCompletionFamily.activeCount_le _

theorem family_value_le
    (μ : FiniteDistribution (PreliminarySampler.Raw clauses branch n t rows repeats))
    (δ : ℚ) (hδ : 0 < δ) :
    (family clauses μ δ).game.value ≤ (CanonicalGame.game F μ).value + (δ : ℝ) / 3 := by
  apply (family clauses μ δ).value_le_of_bound ((δ : ℝ) / 3)
  intro e
  have hδreal : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have h := CompletionParameters.residual_le_third
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)
    (CanonicalLocalCompletion.leftLabel_card_le F δ (CanonicalGame.leftAt F e)) hδreal
    (CompletionAlphabet.size_budget
      (CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t)) δ hδ)
  simp only [Fintype.card_fin]
  rw [Fintype.card_eq_nat_card]
  rw [Fintype.card_eq_nat_card] at h
  simpa only [CanonicalGame.game] using h

theorem family_value_of_satisfying
    (μ : FiniteDistribution (PreliminarySampler.Raw clauses branch n t rows repeats))
    (δ : ℚ) (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    (family clauses μ δ).game.value = 1 := by
  apply (family clauses μ δ).value_eq_one
  exact HierarchicalGame.value_eq_one
    (PreliminarySampler.family clauses branch n t rows repeats) μ assignment hsat

def actualFamily [NeZero m] (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ) :=
  family clauses (PreliminarySampler.law (t := t) clauses rows repeats hn hbranch hrows) δ

def actualValue [NeZero m] (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ) : ℝ :=
  (actualFamily (t := t) clauses rows repeats hn hbranch hrows δ).game.value

theorem actualValue_le [NeZero m] (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (δ : ℚ) (hδ : 0 < δ) :
    actualValue (t := t) clauses rows repeats hn hbranch hrows δ ≤
      (PreliminarySampler.game clauses branch n t rows repeats hn hbranch hrows).value +
        (δ : ℝ) / 3 := by
  exact family_value_le clauses
    (PreliminarySampler.law (t := t) clauses rows repeats hn hbranch hrows) δ hδ

theorem actualValue_of_satisfying [NeZero m] (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (δ : ℚ) (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    actualValue (t := t) clauses rows repeats hn hbranch hrows δ = 1 :=
  family_value_of_satisfying clauses
    (PreliminarySampler.law (t := t) clauses rows repeats hn hbranch hrows) δ assignment hsat

end
end PerfectCompleteness.FinitePreliminaryCompletion

end

end OAI
