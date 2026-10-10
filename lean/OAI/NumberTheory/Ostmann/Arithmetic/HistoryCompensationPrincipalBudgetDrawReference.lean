import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationBiasedKernelSumDrawReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationPrincipalBudgetBiased

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryCompensationPrincipalBudget
open Construction Construction.CanonicalOccurrenceTransport Conclusion Filter
open CompensationEqualityPatterns HistoryCompensationBiasedKernelSum
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_optionalDrawSymbolicKernelSum_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l : ℕ, l ≤ k →
      let seed := Template.initial (2*(bulkSize k L/2)) k
      ∀ (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ)
        (refs : ∀ p : Pattern (pairedHistoryType seed l),
          (Block p → CommonSample C.sources (pairedInternalOrigin seed l)) →
          Option (PatternReference p V outside l))
        (mask : ∀ p : Pattern (pairedHistoryType seed l),
          (Block p → CommonSample C.sources (pairedInternalOrigin seed l)) → ℝ),
      (∀ p b, 0 ≤ mask p b ∧ mask p b ≤ 1) →
      biasedKernelSum C.sources (pairedInternalOrigin seed l) (pairedHistoryType seed l)
        (optionalDrawSymbolicPatternKernel C.sources (pairedInternalOrigin seed l)
          (pairedHistoryType seed l) mixed V outside l refs) mask ≤
        Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_biasedKernelSum_eventually d Bs BD Bz hk] with L hL
  intro E C hG hGu hcl hcu hb hd l hl
  dsimp only
  intro mixed V outside refs mask hm
  exact hL E C hG hGu hcl hcu hb hd l hl _ mask
    (optionalDrawSymbolicPatternKernel_bounds C.sources _ _ mixed V outside l refs) hm

end Ostmann.Arithmetic.HistoryCompensationPrincipalBudget

end

end OAI
