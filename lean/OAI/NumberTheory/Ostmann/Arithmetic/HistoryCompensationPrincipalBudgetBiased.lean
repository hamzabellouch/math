import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationBiasedKernelSumSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationNormalizationBudget

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryCompensationPrincipalBudget
open Construction Construction.CanonicalOccurrenceTransport Conclusion Filter
open CompensationEqualityPatterns HistoryCompensationBiasedKernelSum
open HistoryCompensationNormalizationBudget
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_biasedKernelSum_eventually
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
      ∀ (K : ∀ p : Pattern (pairedHistoryType seed l),
        (Block p → CommonSample C.sources (pairedInternalOrigin seed l)) → Block p → ℝ)
        (mask : ∀ p : Pattern (pairedHistoryType seed l),
        (Block p → CommonSample C.sources (pairedInternalOrigin seed l)) → ℝ),
      (∀ p b q, 0 ≤ K p b q ∧ K p b q ≤ 2/((b q).val:ℝ)) →
      (∀ p b, 0 ≤ mask p b ∧ mask p b ≤ 1) →
      biasedKernelSum C.sources (pairedInternalOrigin seed l) (pairedHistoryType seed l) K mask ≤
        Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_pattern_universal_eventually d Bs BD Bz hk] with L hL
  intro E C hG hGu hcl hcu hb hd l hl
  dsimp only
  intro K mask hK hm
  exact (selected_biasedKernelSum_le C _ _ K mask hK hm).trans
    (hL E C hG hGu hcl hcu hb hd l hl)

end Ostmann.Arithmetic.HistoryCompensationPrincipalBudget

end

end OAI
