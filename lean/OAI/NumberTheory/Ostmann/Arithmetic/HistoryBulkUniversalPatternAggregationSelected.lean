import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationPrincipalBudgetBiased

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation
open Construction CanonicalOccurrenceTransport Conclusion Filter
open CompensationEqualityPatterns HistoryCompensationBiasedKernelSum HistoryCompensationPrincipalBudget
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
open scoped BigOperators

theorem selected_patternComplexSum_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀l : ℕ,l ≤ k →
      let seed := Template.initial (2*(bulkSize k L/2)) k
      ∀(F : ∀p : Pattern (pairedHistoryType seed l),
        (Block p → CommonSample C.sources (pairedInternalOrigin seed l)) → ℂ)
        (A : ℝ),0 ≤ A →
      (∀p b,patternWeight C.sources (pairedInternalOrigin seed l) p b≠0 →
        Function.Injective (fun q=>(blockType p q,b q)) →
        ‖F p b‖ ≤ A*∏q : Block p,2/((b q).val:ℝ)) →
      ‖patternComplexSum C.sources (pairedInternalOrigin seed l) (pairedHistoryType seed l) F‖ ≤
        A*Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_biasedKernelSum_eventually d Bs BD Bz hk] with L hsum
  intro E C hG hGu hcl hcu hb hd l hl
  dsimp only
  intro F A hA hF
  refine (norm_patternComplexSum_le_kernelSum C.sources _ _ F A hF).trans ?_
  apply mul_le_mul_of_nonneg_left _ hA
  apply hsum E C hG hGu hcl hcu hb hd l hl
  · intro p b q
    exact ⟨div_nonneg (by norm_num) (Nat.cast_nonneg _),le_rfl⟩
  · intro p b
    exact ⟨zero_le_one,le_rfl⟩

end Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation

end

end OAI
