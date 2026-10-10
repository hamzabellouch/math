import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalDecay
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalGoodAbsorption

namespace OAI

open Erdos970

noncomputable section
open Filter
namespace Ostmann.Construction
open Conclusion

theorem selected_diagonal_of_single_and_good_eventually
    (d : Decomposition) (Bs BD Bz Cs : ℝ) {k : ℕ} (hk : 0 < k)
    (hD : 0≤BD) (hBz : 9≤Bz) (hBD : Bs+Cs+105≤BD) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀(spectator : PrimeSource),
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀(s : ℕ)(X : ℝ),∀l<k,
      C.selectedDiagonalSingleEnergy spectator s X l≤
        Real.exp ((2:ℝ)^l*(initialGap Bs k L+Cs*(bulkSize k L:ℝ))) →
      (∀e,InitialSourceChoice.diagonalGoodPermutation (2*(bulkSize k L/2)) k l e →
        ‖C.selectedDiagonalCovariance spectator s X l e‖≤
          Real.exp (-(selectedDiagonalGoodRate k+67*(2:ℝ)^k)*(bulkSize k L:ℝ))) →
      extendedDiagonal d C.favorable C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) C.giant spectator (2*s) X C.giantCenter
        (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin) l≤
        Real.exp (-66*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_diagonal_decay_of_actual_comparisons_eventually d Bs BD Bz Cs
      hk hBz hBD,
    selected_diagonal_good_absorption_eventually d Bs BD Bz hk hD (by linarith)]
    with L hdecay hgood
  intro E C hG hGu hcl hcu hb hd spectator hspec s X l hl hsingle hpairs
  exact hdecay E C hG hGu hcl hcu hb hd spectator hspec s X l hl hsingle
    (hgood E C hG hGu hcl hcu hb hd spectator s X l hl.le hpairs)

end Ostmann.Construction

end

end OAI
