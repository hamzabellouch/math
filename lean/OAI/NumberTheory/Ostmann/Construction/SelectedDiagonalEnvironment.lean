import OAI.NumberTheory.Ostmann.Construction.DiagonalEnvironment
import OAI.NumberTheory.Ostmann.Construction.SelectedCounterpartWindows
import OAI.NumberTheory.Ostmann.Construction.SelectedRemainingBands
import OAI.NumberTheory.Ostmann.Construction.SourceFrequencyBounds

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
open Filter
namespace Ostmann.Construction
open Conclusion
namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

def selectedDiagonalCovariance (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s : ℕ) (X : ℝ) (l : ℕ)
    (e : Equiv.Perm (RemainingIndex
      (Template.remainder (l+1) (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)))) : ℂ :=
  C.diagonalCovariance (Template.initial (2*(bulkSize k L/2)) k)
    (frequencyBound Bs BD Bz k L) spectator (2*s) X
    (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin) l
    (C.compensationLogScale l) (stepGap BD Bz k L l) e

def selectedDiagonalNormalizer (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ) : ℝ :=
  C.remainingNormalization
    (Template.remainder (l+1) (Template.current (Template.initial (2*(bulkSize k L/2)) k) l))*
      Real.exp (-stepGap BD Bz k L l)
end InitialSourceChoice

theorem selected_diagonal_environment_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀(spectator : PrimeSource),
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀(s : ℕ)(X : ℝ),∀l<k,
      extendedDiagonal d C.favorable C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) C.giant spectator (2*s) X C.giantCenter
        (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin) l≤
      C.selectedDiagonalNormalizer l*
        (∑e,C.selectedDiagonalCovariance spectator s X l e).re := by
  filter_upwards [initial_sources_above_frequencies_eventually d Bs BD Bz hk,
    initial_source_cross_role_separation_eventually d Bs BD Bz hk] with L hprime hsep
  intro E C hG hc hcu hb hd spectator hspec s X l hl
  have hfreq := hprime E C hG hc hcu hb hd l hl.le
  exact C.extendedDiagonal_le_covariances
    (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L)
    spectator (2*s) X (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin)
    l (C.compensationLogScale l) (stepGap BD Bz k L l) (fun q hq => hq)
    hfreq.1 (fun i => hfreq.2 _)
    (C.remaining_bandsSeparated spectator (hsep E C hG hc hcu hb hd spectator hspec) l)

end Ostmann.Construction

end

end OAI
