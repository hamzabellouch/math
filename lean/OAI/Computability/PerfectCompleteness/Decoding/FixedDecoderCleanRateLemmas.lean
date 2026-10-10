import OAI.Computability.PerfectCompleteness.Decoding.CleanDecoderRateLemmas
import OAI.Computability.PerfectCompleteness.Repetition.FixedCleanRate

namespace OAI

section

namespace PerfectCompleteness.FixedDecoderCleanRate

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

structure Geometry {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)
    (n h : Nat) (upper : Nodes (FixedParameters.branch p) n)
    (d : HierarchicalFrozenTables.LowerNodes upper (h + 1)) where
  designated : Fin (FixedParameters.branch p h) → Slots (FixedParameters.branch p) h
  cut : OwnInputReference.Cut upper (HierarchicalLeftDecoder.LowerNode upper (h + 1) d)
  outside : Slots (FixedParameters.branch p) n →
    Fin (FixedRows.sourceLength p.plan hδ) → MixedSupport.Slot
  placeholder : Slots (FixedParameters.branch p) (h + 1) →
    Fin (FixedRows.sourceLength p.plan hδ) → MixedSupport.Slot
  exterior : CleanPhysicalReplay.Exterior (FixedRows.rows p.plan) (FixedRows.repeats p.plan)
    (CleanRecordDecoderInput.path upper d cut) outside placeholder

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)
  {n h : Nat} {upper : Nodes (FixedParameters.branch p) n}
  {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (G : Geometry p n h upper d)

def setup (input : List Bool) :
    CleanDecoderRate.Setup (FixedParameters.branch p) (FixedRows.rows p.plan)
      (FixedRows.repeats p.plan) n h (FixedRows.sourceLength p.plan hδ)
      (PCPSource.normalizedFormula (BinaryLanguage.totalRename input)).variables
      (PCPSource.normalizedFormula (BinaryLanguage.totalRename input)).clauses.length
      upper d where
  clauses := PCPSource.clauseFamily (BinaryLanguage.totalRename input)
  designated := G.designated
  cut := G.cut
  outside := G.outside
  placeholder := G.placeholder
  exterior := G.exterior

theorem calls_le (input : List Bool) (hn : n ≤ p.plan.depth) :
    Fintype.card (CleanDecoderRate.Calls (setup p G input)) ≤ FixedParameters.calls p.plan := by
  have hactual := FixedCallBudget.modified_calls_le (FixedRows.rows p.plan)
    (FixedRows.repeats p.plan) (CleanDecoderRate.path (setup p G input)) hn
  apply hactual.trans
  unfold FixedParameters.calls
  omega

theorem cubePositive (height : Nat) : 0 < p.cubeSize height := by
  have hsize := (p.cube_errors height).1
  omega

theorem branchPositive : ∀ k < n, 0 < FixedParameters.branch p k :=
  fun k _ => FixedParameters.branch_pos p k

variable (input : List Bool)
  (σ : KeyStrategy.Strategy
    (TreeCanonical.locationCount (FixedParameters.branch p) n
      (FixedRows.sourceLength p.plan hδ)))
  (useful : (record : CleanDecoderRate.Record (setup p G input)) →
    CleanLeftDecoder.Useful
      (CleanDecoderContext.leftExposed (CleanDecoderRate.context (setup p G input) record))
      upper (h + 1))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block (FixedRows.rows p.plan) upper) r)
  (W : Submodule F2 (OwnInputReference.UpperVector (FixedRows.rows p.plan) upper))
  (a : OwnInputReference.LowerVector (FixedRows.rows p.plan)
    (HierarchicalLeftDecoder.LowerNode upper (h + 1) d))
  (threshold : ℝ)

theorem probability_lt_accuracy (unsat : ¬ BinaryLanguage.language input)
    (hn : n ≤ p.plan.depth) (hρ : 0 < ρ) :
    (CleanDecoderRate.law (setup p G input) σ useful r ρ A W a threshold
      (p.cubeSize h) (cubePositive p h)).probability
        (fun z => CleanDecoderRate.agrees (setup p G input) (branchPositive p)
          (FixedRows.cutoff p.plan hδ) z.1 z.2) < p.accuracy := by
  have hbound := CleanDecoderRate.bound (setup p G input) σ useful r ρ A W a threshold
    (branchPositive p) (cubePositive p h) hρ (FixedParameters.source_rate p input unsat)
  apply hbound.trans_lt
  simpa only [FixedParameters.branch] using
    FixedCleanRate.actual_clean_error p (calls_le p G input hn) h

end
end PerfectCompleteness.FixedDecoderCleanRate

end

section

namespace PerfectCompleteness.FixedDecoderPairRate

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays FixedDecoderCleanRate

abbrev F2 := ZMod 2

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)
  {n h : Nat} {upper : Nodes (FixedParameters.branch p) n}
  {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (G : Geometry p n h upper d)
  (input : List Bool)
  (σ : KeyStrategy.Strategy
    (TreeCanonical.locationCount (FixedParameters.branch p) n
      (FixedRows.sourceLength p.plan hδ)))
  (useful : (record : CleanDecoderRate.Record (setup p G input)) →
    CleanLeftDecoder.Useful
      (CleanDecoderContext.leftExposed (CleanDecoderRate.context (setup p G input) record))
      upper (h + 1))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block (FixedRows.rows p.plan) upper) r)
  (W : Submodule F2 (OwnInputReference.UpperVector (FixedRows.rows p.plan) upper))
  (a : OwnInputReference.LowerVector (FixedRows.rows p.plan)
    (HierarchicalLeftDecoder.LowerNode upper (h + 1) d))
  (threshold : ℝ)

theorem probability_lt_accuracy (unsat : ¬ BinaryLanguage.language input)
    (hn : n ≤ p.plan.depth) (hρ : 0 < ρ) :
    (CleanDecoderPairLaw.pairLaw (setup p G input) σ useful r ρ A W a threshold
      (p.cubeSize h) (cubePositive p h)).probability
        (fun z => CleanDecoderPairLaw.pairAgrees (setup p G input) (branchPositive p)
          (FixedRows.cutoff p.plan hδ) z.1 z.2) < p.accuracy := by
  rw [CleanDecoderPairLaw.pair_probability_eq]
  exact FixedDecoderCleanRate.probability_lt_accuracy p G input σ useful r ρ A W a threshold
    unsat hn hρ

end
end PerfectCompleteness.FixedDecoderPairRate

end

end OAI
