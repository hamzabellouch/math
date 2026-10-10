import Mathlib.Data.Fintype.Sigma
import OAI.Computability.PerfectCompleteness.Decoding.HierarchicalDecoderTables

namespace OAI

section

namespace PerfectCompleteness.HierarchicalAllDecoderTables

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

private theorem row_probability_of_raw {Q A : Type*} [Fintype A]
    (μ : FiniteDistribution (Option A)) (valid : Q → A → Prop) (q : Q)
    (predicate : A → Prop) (hp : valid q = predicate)
    (hv : μ.probability (fun answer => decide
      (∀ z, answer = some z → predicate z)) = 1) :
    μ.probability (fun answer => decide
      (DecoderTableAdmissibility.RowValid valid q answer)) = 1 := by
  have hevent : (fun answer : Option A => decide
      (DecoderTableAdmissibility.RowValid valid q answer)) =
      (fun answer : Option A => decide (∀ z, answer = some z → predicate z)) := by
    funext answer
    apply (@decide_eq_decide
      (DecoderTableAdmissibility.RowValid valid q answer)
      (∀ z, answer = some z → predicate z) _ _).mpr
    unfold DecoderTableAdmissibility.RowValid
    rw [hp]
  rw [hevent]
  exact hv

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

abbrev Background := HierarchicalMatrixTable.Background (rows := rows) slots upper

abbrev Input (r : Nat) :=
  (background : Background (rows := rows) slots upper) ×
    HierarchicalDecoderTables.Advice slots upper lowerLevel background r

local instance rowSpaceFintype (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace slots node) := Fintype.ofFinite _

local instance nodeSpaceFintype (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH slots node) := Fintype.ofFinite _

instance inputFintype (r : Nat) : Fintype (Input (rows := rows) slots upper lowerLevel r) := by
  letI : Fintype (Background (rows := rows) slots upper) := Fintype.ofFinite _
  letI : (background : Background (rows := rows) slots upper) →
      Fintype (HierarchicalDecoderTables.Advice slots upper lowerLevel background r) :=
    fun _ => inferInstance
  exact inferInstanceAs (Fintype
    ((background : Background (rows := rows) slots upper) ×
      HierarchicalDecoderTables.Advice slots upper lowerLevel background r))

abbrev UpperAnswer := Module.Dual F2 (NodeEmbedding.RowSpace slots upper)

local instance upperDualFintype : Fintype (UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

local instance answerFintype (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (HierarchicalDecoderTables.Answer slots upper lowerLevel d) :=
  LeftDecoder.dualFintype
    (V := squareSpace (HierarchicalDecoderTables.LowerH slots upper lowerLevel d))

variable (hbranch : ∀ k < n, 0 < branch k)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (background : Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background → Prop)

def upperKernel (r : Nat) (ρ : ℝ) (input : Input (rows := rows) slots upper lowerLevel r) :
    FiniteDistribution (UpperAnswer slots upper) :=
  HierarchicalLeftDecoder.adviceLaw slots upper lowerLevel input.1 σ (useful input.1)
    r ρ input.2.1 input.2.2

def upperTableLaw (r : Nat) (ρ : ℝ) :
    FiniteDistribution (Input (rows := rows) slots upper lowerLevel r → UpperAnswer slots upper) :=
  FiniteDistribution.table (upperKernel slots upper lowerLevel σ useful r ρ)

def decodeTable (r : Nat)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (table : Input (rows := rows) slots upper lowerLevel r → UpperAnswer slots upper) :
    Input (rows := rows) slots upper lowerLevel r →
      Option (HierarchicalDecoderTables.Answer slots upper lowerLevel d) :=
  fun input => HierarchicalDecoderTables.decode slots upper lowerLevel hbranch d s (table input)

def responseLaw (r : Nat) (ρ : ℝ)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (input : Input (rows := rows) slots upper lowerLevel r) :
    FiniteDistribution (Option (HierarchicalDecoderTables.Answer slots upper lowerLevel d)) :=
  (upperKernel slots upper lowerLevel σ useful r ρ input).pushforward
    (HierarchicalDecoderTables.decode slots upper lowerLevel hbranch d s)

def tableLaw (r : Nat) (ρ : ℝ)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat) :
    FiniteDistribution (Input (rows := rows) slots upper lowerLevel r →
      Option (HierarchicalDecoderTables.Answer slots upper lowerLevel d)) :=
  FiniteDistribution.table (responseLaw slots upper lowerLevel hbranch σ useful r ρ d s)

theorem upperTableLaw_pushforward (r : Nat) (ρ : ℝ)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat) :
    (upperTableLaw slots upper lowerLevel σ useful r ρ).pushforward
      (decodeTable slots upper lowerLevel hbranch r d s) =
        tableLaw slots upper lowerLevel hbranch σ useful r ρ d s := by
  exact CleanConditioning.pushforward_law
    (I := Input (rows := rows) slots upper lowerLevel r)
    (Ω := fun _ => UpperAnswer slots upper)
    (Γ := fun _ => Option (HierarchicalDecoderTables.Answer slots upper lowerLevel d))
    (upperKernel slots upper lowerLevel σ useful r ρ)
    (fun _ => HierarchicalDecoderTables.decode slots upper lowerLevel hbranch d s)

theorem supported_upper_table_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (table : Input (rows := rows) slots upper lowerLevel r → UpperAnswer slots upper)
    (hsupport : (upperTableLaw slots upper lowerLevel σ useful r ρ).weight table ≠ 0)
    (input : Input (rows := rows) slots upper lowerLevel r) :
    HierarchicalLeftDecoder.Valid slots upper lowerLevel hbranch input.1 (table input) := by
  have hrow := FiniteDistribution.table_row_weight_ne_zero
    (upperKernel slots upper lowerLevel σ useful r ρ) table hsupport input
  exact of_decide_eq_true (DecoderTableAdmissibility.event_of_probability_one
    (upperKernel slots upper lowerLevel σ useful r ρ input)
    (fun q => decide (HierarchicalLeftDecoder.Valid slots upper lowerLevel hbranch input.1 q))
    (HierarchicalLeftDecoder.adviceLaw_valid slots upper lowerLevel hbranch input.1
      σ (useful input.1) r ρ hρ input.2.1 input.2.2) (table input) hrow)

theorem upperTableLaw_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ) :
    (upperTableLaw slots upper lowerLevel σ useful r ρ).probability
      (fun table => decide (∀ input : Input (rows := rows) slots upper lowerLevel r,
        HierarchicalLeftDecoder.Valid slots upper lowerLevel hbranch input.1 (table input))) = 1 := by
  apply DecoderTableAdmissibility.probability_one_of_support
  intro table hsupport
  exact decide_eq_true (supported_upper_table_valid slots upper lowerLevel hbranch σ useful
    r ρ hρ table hsupport)

def RowValid (r : Nat) (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (input : Input (rows := rows) slots upper lowerLevel r)
    (z : HierarchicalDecoderTables.Answer slots upper lowerLevel d) : Prop :=
  HierarchicalDecoderTables.Valid slots upper lowerLevel input.1 hbranch d s z

theorem responseLaw_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (input : Input (rows := rows) slots upper lowerLevel r) :
    (responseLaw slots upper lowerLevel hbranch σ useful r ρ d s input).probability
      (fun answer => decide (DecoderTableAdmissibility.RowValid
        (RowValid slots upper lowerLevel hbranch r d s) input answer)) = 1 := by
  have hlaw : responseLaw slots upper lowerLevel hbranch σ useful r ρ d s input =
      HierarchicalDecoderTables.responseLaw slots upper lowerLevel input.1 hbranch
        σ (useful input.1) r ρ d s input.2 := rfl
  rw [hlaw]
  apply row_probability_of_raw
    (Q := Input (rows := rows) slots upper lowerLevel r)
    (A := HierarchicalDecoderTables.Answer slots upper lowerLevel d)
    (HierarchicalDecoderTables.responseLaw slots upper lowerLevel input.1 hbranch
      σ (useful input.1) r ρ d s input.2)
    (RowValid slots upper lowerLevel hbranch r d s) input
    (HierarchicalDecoderTables.Valid slots upper lowerLevel input.1 hbranch d s) rfl
  rw [← HierarchicalDecoderTables.responseLaw_valid slots upper lowerLevel input.1 hbranch
    σ (useful input.1) r ρ hρ d s input.2]
  apply congrArg (HierarchicalDecoderTables.responseLaw slots upper lowerLevel input.1 hbranch
    σ (useful input.1) r ρ d s input.2).probability
  funext answer
  exact (@decide_eq_decide _ _ _ _).mpr Iff.rfl

theorem supported_table_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (table : Input (rows := rows) slots upper lowerLevel r →
      Option (HierarchicalDecoderTables.Answer slots upper lowerLevel d))
    (hsupport : (tableLaw slots upper lowerLevel hbranch σ useful r ρ d s).weight table ≠ 0) :
    DecoderTableAdmissibility.Admissible (RowValid slots upper lowerLevel hbranch r d s) table := by
  exact DecoderTableAdmissibility.table_admissible_of_probability_one
    (responseLaw slots upper lowerLevel hbranch σ useful r ρ d s)
    (RowValid slots upper lowerLevel hbranch r d s)
    (responseLaw_valid slots upper lowerLevel hbranch σ useful r ρ hρ d s) table hsupport

theorem tableLaw_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat) :
    (tableLaw slots upper lowerLevel hbranch σ useful r ρ d s).probability
      (fun table => decide (DecoderTableAdmissibility.Admissible
        (RowValid slots upper lowerLevel hbranch r d s) table)) = 1 :=
  DecoderTableAdmissibility.table_admissible_probability_one
    (responseLaw slots upper lowerLevel hbranch σ useful r ρ d s)
    (RowValid slots upper lowerLevel hbranch r d s)
    (responseLaw_valid slots upper lowerLevel hbranch σ useful r ρ hρ d s)

theorem decoded_supported_table_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (table : Input (rows := rows) slots upper lowerLevel r → UpperAnswer slots upper)
    (hsupport : (upperTableLaw slots upper lowerLevel σ useful r ρ).weight table ≠ 0)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat) :
    DecoderTableAdmissibility.Admissible (RowValid slots upper lowerLevel hbranch r d s)
      (decodeTable slots upper lowerLevel hbranch r d s table) := by
  intro input z hz
  exact HierarchicalDecoderTables.decode_valid slots upper lowerLevel input.1 hbranch d s
    (table input) (supported_upper_table_valid slots upper lowerLevel hbranch σ useful
      r ρ hρ table hsupport input) z hz

end
end PerfectCompleteness.HierarchicalAllDecoderTables

end

end OAI
