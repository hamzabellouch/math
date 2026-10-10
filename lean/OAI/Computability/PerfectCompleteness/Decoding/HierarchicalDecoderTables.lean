import OAI.Computability.PerfectCompleteness.Decoding.HierarchicalLeftDecoder
import OAI.Computability.PerfectCompleteness.Foundations.MultiplicationFormInjectiveLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanConditioning

namespace OAI

section

namespace PerfectCompleteness.HierarchicalDecoderTables

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

section ConstantValidity

variable {Q A Ω : Type*} [Fintype Q] [DecidableEq Q] [Fintype A] [Fintype Ω]

omit [Fintype Q] [DecidableEq Q] in
private theorem constant_row_event_eq (valid : A → Prop) (q : Q) :
    (fun answer : Option A => decide
      (DecoderTableAdmissibility.RowValid (fun (_ : Q) => valid) q answer)) =
      (fun answer : Option A => decide (∀ z, answer = some z → valid z)) := by
  funext answer
  exact (@decide_eq_decide
    (DecoderTableAdmissibility.RowValid (fun (_ : Q) => valid) q answer)
    (∀ z, answer = some z → valid z) _ _).mpr Iff.rfl

private theorem table_admissible_of_constant_probability_one
    (responses : Q → FiniteDistribution (Option A)) (valid : A → Prop)
    (hvalid : ∀ q, (responses q).probability
      (fun answer => decide (∀ z, answer = some z → valid z)) = 1)
    (table : Q → Option A)
    (hsupport : (FiniteDistribution.table responses).weight table ≠ 0) :
    DecoderTableAdmissibility.Admissible (fun (_ : Q) => valid) table := by
  apply DecoderTableAdmissibility.table_admissible_of_probability_one
    responses (fun (_ : Q) => valid) _ table hsupport
  intro q
  exact (congrArg (responses q).probability (constant_row_event_eq valid q)).trans (hvalid q)

private theorem hit_square_le_of_constant_probability_one
    (responses : Q → FiniteDistribution (Option A))
    (ν : FiniteDistribution Ω) (ownInput : Ω → Q) (right : A)
    (valid : A → Prop)
    (hvalid : ∀ q, (responses q).probability
      (fun answer => decide (∀ z, answer = some z → valid z)) = 1)
    (bound : ℝ)
    (hbound : ∀ table : Q → Option A,
      DecoderTableAdmissibility.Admissible (fun (_ : Q) => valid) table →
      StochasticSingleResponse.tableCollision ν ownInput table ≤ bound) :
    StochasticSingleResponse.hit responses ν ownInput right ^ 2 ≤ bound := by
  apply StochasticSingleResponse.hit_square_le_of_probability_one
    responses ν ownInput right (fun (_ : Q) => valid) _ bound hbound
  intro q
  exact (congrArg (responses q).probability (constant_row_event_eq valid q)).trans (hvalid q)

end ConstantValidity

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

local instance rowSpaceFintype (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace slots node) := Fintype.ofFinite _

local instance nodeSpaceFintype (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH slots node) := Fintype.ofFinite _

local instance upperDualFintype :
    Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

abbrev Advice (r : Nat) :=
  ManyGoodRows.RowMap (Block rows upper) r ×
    (Module.Dual F2 (NodeEmbedding.RowSpace slots upper ⧸
      HierarchicalFrozenTables.knownRows slots upper lowerLevel background) →ₗ[F2]
      (Fin r → F2))

local instance adviceFintype (r : Nat) :
    Fintype (Advice slots upper lowerLevel background r) := by
  letI : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper ⧸
      HierarchicalFrozenTables.knownRows slots upper lowerLevel background)) :=
    LeftDecoder.dualFintype
  infer_instance

variable (hbranch : ∀ k < n, 0 < branch k)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background → Prop)

abbrev LowerH (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :=
  NodeEmbedding.NodeH slots (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)

abbrev Answer (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :=
  Module.Dual F2 (squareSpace (LowerH slots upper lowerLevel d))

local instance answerFintype (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (Answer slots upper lowerLevel d) :=
  LeftDecoder.dualFintype (V := squareSpace (LowerH slots upper lowerLevel d))

def fullRank (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (z : Answer slots upper lowerLevel d) : Nat :=
  OddListExtraction.formRank (LowerH slots upper lowerLevel d)
    (OddListExtraction.multiplicationForm (LowerH slots upper lowerLevel d) z)

def decode (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :
    Option (Answer slots upper lowerLevel d) :=
  let z := HierarchicalLeftDecoder.output slots upper lowerLevel hbranch d q
  if fullRank slots upper lowerLevel d z ≤ s then none else some z

def responseLaw (r : Nat) (ρ : ℝ)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (advice : Advice slots upper lowerLevel background r) :
    FiniteDistribution (Option (Answer slots upper lowerLevel d)) :=
  (HierarchicalLeftDecoder.adviceLaw slots upper lowerLevel background σ useful r ρ
    advice.1 advice.2).pushforward (decode slots upper lowerLevel hbranch d s)

def Valid (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (z : Answer slots upper lowerLevel d) : Prop :=
  z (HierarchicalLeftDecoder.lowerOne slots upper lowerLevel hbranch d) = 1 ∧
    (LowerAffineSliceRank.testedGram
      (FunctionSpaceLowerRank.matrixForm (LowerH slots upper lowerLevel d)
        (OddListExtraction.multiplicationForm (LowerH slots upper lowerLevel d) z))
      (HierarchicalLeftDecoder.testedMatrix slots upper lowerLevel background d)).rank ≤ 1 ∧
    s < fullRank slots upper lowerLevel d z

theorem decode_valid
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (hq : HierarchicalLeftDecoder.Valid slots upper lowerLevel hbranch background q)
    (z : Answer slots upper lowerLevel d)
    (hz : decode slots upper lowerLevel hbranch d s q = some z) :
    Valid slots upper lowerLevel background hbranch d s z := by
  change (if fullRank slots upper lowerLevel d
      (HierarchicalLeftDecoder.output slots upper lowerLevel hbranch d q) ≤ s then none
    else some (HierarchicalLeftDecoder.output slots upper lowerLevel hbranch d q)) = some z at hz
  split at hz
  · cases hz
  · rename_i hrank
    have heq := Option.some.inj hz
    subst z
    exact ⟨(hq d).1, (hq d).2, Nat.lt_of_not_ge hrank⟩

theorem responseLaw_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (advice : Advice slots upper lowerLevel background r) :
    (responseLaw slots upper lowerLevel background hbranch σ useful r ρ d s advice).probability
      (fun answer => decide (∀ z, answer = some z →
        Valid slots upper lowerLevel background hbranch d s z)) = 1 := by
  rw [responseLaw, FiniteDistribution.probability_pushforward]
  apply le_antisymm (FiniteDistribution.probability_le_one _ _)
  rw [← HierarchicalLeftDecoder.adviceLaw_valid slots upper lowerLevel hbranch background
    σ useful r ρ hρ advice.1 advice.2]
  apply FiniteDistribution.probability_mono
  intro q hq
  apply decide_eq_true
  intro z hz
  exact decode_valid slots upper lowerLevel background hbranch d s q
    (of_decide_eq_true hq) z hz

def tableLaw (r : Nat) (ρ : ℝ)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat) :
    FiniteDistribution (Advice slots upper lowerLevel background r →
      Option (Answer slots upper lowerLevel d)) :=
  FiniteDistribution.table
    (responseLaw slots upper lowerLevel background hbranch σ useful r ρ d s)

def upperTableLaw (r : Nat) (ρ : ℝ) :
    FiniteDistribution (Advice slots upper lowerLevel background r →
      Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  FiniteDistribution.table (fun advice : Advice slots upper lowerLevel background r =>
    HierarchicalLeftDecoder.adviceLaw slots upper lowerLevel background σ useful
      r ρ advice.1 advice.2)

theorem upperTableLaw_pushforward (r : Nat) (ρ : ℝ)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat) :
    (upperTableLaw slots upper lowerLevel background σ useful r ρ).pushforward
      (fun table advice => decode slots upper lowerLevel hbranch d s (table advice)) =
        tableLaw slots upper lowerLevel background hbranch σ useful r ρ d s := by
  exact CleanConditioning.pushforward_law
    (fun advice : Advice slots upper lowerLevel background r =>
      HierarchicalLeftDecoder.adviceLaw slots upper lowerLevel background σ useful
        r ρ advice.1 advice.2)
    (fun _ => decode slots upper lowerLevel hbranch d s)

theorem supported_table_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (table : Advice slots upper lowerLevel background r → Option (Answer slots upper lowerLevel d))
    (hsupport : (tableLaw slots upper lowerLevel background hbranch σ useful r ρ d s).weight table ≠ 0) :
    DecoderTableAdmissibility.Admissible
      (Q := Advice slots upper lowerLevel background r)
      (A := Answer slots upper lowerLevel d)
      (fun (_ : Advice slots upper lowerLevel background r)
        (z : Answer slots upper lowerLevel d) =>
        Valid slots upper lowerLevel background hbranch d s z) table := by
  apply table_admissible_of_constant_probability_one
    (Q := Advice slots upper lowerLevel background r)
    (A := Answer slots upper lowerLevel d)
    (responseLaw slots upper lowerLevel background hbranch σ useful r ρ d s)
    (Valid slots upper lowerLevel background hbranch d s)
    _ table hsupport
  intro advice
  rw [← responseLaw_valid slots upper lowerLevel background hbranch σ useful r ρ hρ d s advice]
  apply congrArg (responseLaw slots upper lowerLevel background hbranch σ useful r ρ d s
    advice).probability
  funext answer
  exact (@decide_eq_decide _ _ _ _).mpr Iff.rfl

theorem hit_square_le {Ω : Type*} [Fintype Ω]
    (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (ν : FiniteDistribution Ω) (ownInput : Ω → Advice slots upper lowerLevel background r)
    (right : Answer slots upper lowerLevel d) (bound : ℝ)
    (hbound : ∀ table : Advice slots upper lowerLevel background r →
        Option (Answer slots upper lowerLevel d),
      DecoderTableAdmissibility.Admissible
        (Q := Advice slots upper lowerLevel background r)
        (A := Answer slots upper lowerLevel d)
        (fun (_ : Advice slots upper lowerLevel background r)
          (z : Answer slots upper lowerLevel d) =>
          Valid slots upper lowerLevel background hbranch d s z) table →
      StochasticSingleResponse.tableCollision
        (Q := Advice slots upper lowerLevel background r)
        (A := Answer slots upper lowerLevel d) (Ω := Ω) ν ownInput table ≤ bound) :
    StochasticSingleResponse.hit
      (Q := Advice slots upper lowerLevel background r)
      (A := Answer slots upper lowerLevel d) (Ω := Ω)
      (responseLaw slots upper lowerLevel background hbranch σ useful r ρ d s)
      ν ownInput right ^ 2 ≤ bound := by
  apply hit_square_le_of_constant_probability_one
    (Q := Advice slots upper lowerLevel background r)
    (A := Answer slots upper lowerLevel d) (Ω := Ω)
    (responseLaw slots upper lowerLevel background hbranch σ useful r ρ d s)
    ν ownInput right (Valid slots upper lowerLevel background hbranch d s)
    _ bound hbound
  intro advice
  rw [← responseLaw_valid slots upper lowerLevel background hbranch σ useful r ρ hρ d s advice]
  apply congrArg (responseLaw slots upper lowerLevel background hbranch σ useful r ρ d s
    advice).probability
  funext answer
  exact (@decide_eq_decide _ _ _ _).mpr Iff.rfl

end
end PerfectCompleteness.HierarchicalDecoderTables

end

end OAI
