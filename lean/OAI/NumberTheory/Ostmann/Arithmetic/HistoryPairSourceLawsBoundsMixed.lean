import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsBoundsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsMixed

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction CompensationEqualityPatterns HistorySelectedFlagMassBounds
variable {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]

omit [DecidableEq ι] [Fintype ρ] [DecidableEq ρ] in

theorem mixedMass_bounds (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    {k : ℕ} {L : ℝ}
    (hg : ∀ b, Bounds k L (giants b).law.mass)
    (hr : ∀ i, Bounds k L (roots i).law.mass)
    (hb : ∀ q, Bounds k L (biasedBlockWeight sources origin p q))
    (i : SourceIndex ρ (Block p)) :
    SupportBounds k L (mixedSupport giants roots sources origin p i)
      (mixedMass giants roots sources origin p i) := by
  apply integerWeight_bounds _ (mixedValue_injective giants roots sources origin p i)
  rcases i with b | i | q
  · exact hg b
  · exact hr i
  · exact hb q

end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI
