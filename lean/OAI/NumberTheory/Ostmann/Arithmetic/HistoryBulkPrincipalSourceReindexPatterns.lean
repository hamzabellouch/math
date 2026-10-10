import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatternsTests
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationOriginalPatterns

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindex
open Construction CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryBulkUniversalPatternAggregation
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def occurrenceJacobian (sources : SourceFamily) (origin : ι → ℕ)
    (w : ι → CommonSample sources origin) : ℂ :=
  ((∏i,((w i).val:ℝ):ℝ):ℂ)

omit [DecidableEq ι] in
theorem occurrenceJacobian_ne_zero [DecidableEq ι] (sources : SourceFamily) (origin : ι → ℕ)
    (w : ι → CommonSample sources origin) : occurrenceJacobian sources origin w≠0 := by
  apply Complex.ofReal_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast (commonSample_prime sources origin (w i)).ne_zero

def sourcePatternValue (sources : SourceFamily) (origin τ : ι → ℕ)
    (F : IndependentSamples sources origin → ℂ)
    (p : Pattern τ) (b : Block p → CommonSample sources origin) : ℂ :=
  extendSourceTest sources origin F (fun i=>b (label p i)) /
    occurrenceJacobian sources origin (fun i=>b (label p i))

omit [DecidableEq ι] in
theorem originalPatternTest_sourcePatternValue [DecidableEq ι]
    (sources : SourceFamily) (origin τ : ι → ℕ)
    (F : IndependentSamples sources origin → ℂ) (w : ι → CommonSample sources origin) :
    originalPatternTest sources origin τ (sourcePatternValue sources origin τ F) w =
      extendSourceTest sources origin F w / occurrenceJacobian sources origin w := rfl

theorem source_cmean_eq_patternComplexSum (sources : SourceFamily) (origin τ : ι → ℕ)
    (F : IndependentSamples sources origin → ℂ) :
    (dependentProductPrior (fun i=>(sources (origin i)).law)).cmean F =
      patternComplexSum sources origin τ (sourcePatternValue sources origin τ F) := by
  rw [←original_source_pattern_cmean_eq_patternComplexSum]
  apply congrArg (dependentProductPrior (fun i=>(sources (origin i)).law)).cmean
  funext x
  rw [originalPatternTest_sourcePatternValue,extendSourceTest_tupleEmbed]
  change F x=occurrenceJacobian sources origin (tupleEmbed sources origin x) *
    (F x/occurrenceJacobian sources origin (tupleEmbed sources origin x))
  rw [←mul_div_assoc,mul_comm (occurrenceJacobian sources origin _) (F x),
    mul_div_cancel_right₀ _ (occurrenceJacobian_ne_zero sources origin _)]

theorem patternComplexSum_sum {κ : Type*} [Fintype κ]
    (sources : SourceFamily) (origin τ : ι → ℕ)
    (F : κ → ∀p : Pattern τ,(Block p → CommonSample sources origin) → ℂ) :
    patternComplexSum sources origin τ (fun p b=>∑i,F i p b) =
      ∑i,patternComplexSum sources origin τ (F i) := by
  classical
  unfold patternComplexSum
  calc
    _ = ∑p : Pattern τ,∑b : Block p → CommonSample sources origin,
        ∑i:κ,(patternWeight sources origin p b:ℂ)*
          (if Function.Injective (fun q=>(blockType p q,b q)) then F i p b else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp only [Finset.mul_sum,Finset.sum_const_zero,mul_zero]
    _ = ∑p : Pattern τ,∑i:κ,∑b : Block p → CommonSample sources origin,
        (patternWeight sources origin p b:ℂ)*
          (if Function.Injective (fun q=>(blockType p q,b q)) then F i p b else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

end Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindex

end

end OAI
