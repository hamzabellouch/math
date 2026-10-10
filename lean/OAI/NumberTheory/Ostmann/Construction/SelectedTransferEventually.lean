import OAI.NumberTheory.Ostmann.Construction.SelectedTransfer
import OAI.NumberTheory.Ostmann.Construction.SourceFrequencyBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter Conclusion

theorem selected_transfer_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀(spectator : PrimeSource)(s : ℕ)(X : ℝ),∀l<k,
      Real.exp (Real.log (logCellMass C.giantCenter ∅))*
        ‖decompositionAmplitude d C.favorable C.sources (frequencyBound Bs BD Bz k L)
          C.giant spectator X C.giantCenter (bulkSize k L/2) s k C.bulkBin C.spectatorBin l‖^2≤
        extendedDiagonal d C.favorable C.sources (Template.initial (2*(bulkSize k L/2)) k)
          (frequencyBound Bs BD Bz k L) C.giant spectator (2*s) X C.giantCenter
          (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin) l+
        ‖decompositionAmplitude d C.favorable C.sources (frequencyBound Bs BD Bz k L)
          C.giant spectator X C.giantCenter (bulkSize k L/2) s k C.bulkBin C.spectatorBin (l+1)‖ := by
  have hs := (Real.tendsto_sqrt_atTop.comp (bulkSize_tendsto_atTop hk)).eventually
    (eventually_ge_atTop (20+10*(k:ℝ)+Real.log 2))
  filter_upwards [initial_sources_above_frequencies_eventually d Bs BD Bz hk,hs] with L hprime hL
  intro E C hG hc hcu hb hd spectator s X l hl
  exact C.transfer_of_prime_bounds spectator s l hl hL X (hprime E C hG hc hcu hb hd)

end Ostmann.Construction

end

end OAI
