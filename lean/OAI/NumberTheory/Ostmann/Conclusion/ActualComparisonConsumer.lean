import OAI.NumberTheory.Ostmann.Conclusion.ActualComparisonContradiction
import OAI.NumberTheory.Ostmann.Conclusion.ActualParameterChoice
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalComparisonConsumer

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open Construction Filter

theorem selected_arithmetic_comparisons_incompatible_eventually (d : Decomposition)
    (Bs BD Bz Cs Ccov : ℝ) (hBs : 0≤Bs) (hBD : 0≤BD) (hBz : 9≤Bz)
    (hgap : Bs+Cs+105≤BD) {k : ℕ} (hk : 2≤k)
    (hrate : finalRate BD Bs Bz (Ccov+2) k < -66) :
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
      ∀s : ℕ,
      Real.exp (-28*(bulkSize k L:ℝ))≤
        ‖decompositionAmplitude d C.favorable C.sources (frequencyBound Bs BD Bz k L)
          C.giant spectator C.scale C.giantCenter (bulkSize k L/2) s k C.bulkBin C.spectatorBin 0‖ →
      (∀j<k,C.selectedDiagonalSingleEnergy spectator s C.scale j≤
        Real.exp ((2:ℝ)^j*(initialGap Bs k L+Cs*(bulkSize k L:ℝ)))) →
      (∀j<k,∀e,InitialSourceChoice.diagonalGoodPermutation (2*(bulkSize k L/2)) k j e →
        ‖C.selectedDiagonalCovariance spectator s C.scale j e‖≤
          Real.exp (-(selectedDiagonalGoodRate k+67*(2:ℝ)^k)*(bulkSize k L:ℝ))) →
      (∀a b,TransferBadArrangement (a⁻¹*b) → selectedCovariance C spectator s k a b≤
        Real.exp ((2:ℝ)^k*(initialGap Bs k L+Ccov*(bulkSize k L:ℝ))+(bulkSize k L:ℝ))) →
      (∀a b,¬TransferBadArrangement (a⁻¹*b) → selectedCovariance C spectator s k a b≤
        Real.exp (-(frequencyBudget Bs BD Bz k L k+65*(2:ℝ)^k*(bulkSize k L:ℝ)))) → False := by
  filter_upwards [selected_comparisons_incompatible_eventually d Bs BD Bz Ccov
      hBs hBD (by linarith) hk hrate,
    selected_diagonal_of_single_and_good_eventually d Bs BD Bz Cs (by omega : 0<k)
      hBD hBz hgap] with L hcontra hdiag
  intro E C hG hGu hcl hcu hb hd spectator hspec s hinit hsingle hdiaggood hbad hgood
  apply hcontra E C hG hGu hcl hcu hb hd spectator s hinit _ hbad hgood
  intro j hj
  exact (hdiag E C hG hGu hcl hcu hb hd spectator hspec s C.scale j hj
    (hsingle j hj) (hdiaggood j hj)).trans (actual_diagonal_exponential_le_required k j L)

end Ostmann.Conclusion

end

end OAI
