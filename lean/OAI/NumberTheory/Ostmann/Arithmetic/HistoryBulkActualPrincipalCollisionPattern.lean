import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationOriginalBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPattern
open Construction CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryBulkPrincipalCollisionError HistoryBulkUniversalPatternAggregation
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

theorem originalPrincipalSum_eq_patternComplexSum
    (sources : SourceFamily) (origin τ : ι → ℕ)
    (mask : ∀ p : Pattern τ, (Block p → CommonSample sources origin) → ℝ)
    (test : ∀ p : Pattern τ, (Block p → CommonSample sources origin) → ℂ) :
    originalPrincipalSum sources origin τ mask (fun p b => test p b.val) =
      patternComplexSum sources origin τ (fun p b => (mask p b : ℂ) * test p b) := by
  unfold originalPrincipalSum
  exact sum_pattern_original_eq_patternComplexSum sources origin τ
    (fun p b => (mask p b : ℂ) * test p b)

theorem originalBulkPrincipalSum_eq_patternComplexSum
    (sources : SourceFamily) (origin τ : ι → ℕ) (μ : FinitePrior Ω)
    (mask : Ω → ∀ p : Pattern τ, (Block p → CommonSample sources origin) → ℝ)
    (test : Ω → ∀ p : Pattern τ, (Block p → CommonSample sources origin) → ℂ) :
    originalBulkPrincipalSum sources origin τ μ mask (fun u p b => test u p b.val) =
      patternComplexSum sources origin τ (fun p b => μ.cmean (fun u =>
        (mask u p b : ℂ) * test u p b)) := by
  unfold originalBulkPrincipalSum
  exact sum_pattern_original_eq_patternComplexSum sources origin τ
    (fun p b => μ.cmean (fun u => (mask u p b : ℂ) * test u p b))

theorem patternComplexSum_eq_originalBulkPrincipalSum
    (sources : SourceFamily) (origin τ : ι → ℕ) (μ : FinitePrior Ω)
    (mask : Ω → ∀ p : Pattern τ, (Block p → CommonSample sources origin) → ℝ)
    (test : Ω → ∀ p : Pattern τ, (Block p → CommonSample sources origin) → ℂ) :
    patternComplexSum sources origin τ (fun p b => μ.cmean (fun u =>
        (mask u p b : ℂ) * test u p b)) =
      originalBulkPrincipalSum sources origin τ μ mask (fun u p b => test u p b.val) :=
  (originalBulkPrincipalSum_eq_patternComplexSum sources origin τ μ mask test).symm

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPattern

end

end OAI
