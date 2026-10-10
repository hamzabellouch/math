import OAI.NumberTheory.Ostmann.Conclusion.ActualFinalUpper
import OAI.NumberTheory.Ostmann.Conclusion.RegularNormActual

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open Construction Filter

theorem selected_final_upper_of_actual_covariance_eventually (d : Decomposition)
    (Bs BD Bz Ccov : ℝ) (hBs : 0≤Bs) (hBD : 0≤BD) (hBz : 0≤Bz)
    {k : ℕ} (hk : 2≤k) (hrate : finalRate BD Bs Bz (Ccov+2) k < -66) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀(spectator : PrimeSource)(s : ℕ),
      (∀a b,TransferBadArrangement (a⁻¹*b) → selectedCovariance C spectator s k a b≤
        Real.exp ((2:ℝ)^k*(initialGap Bs k L+Ccov*(bulkSize k L:ℝ))+(bulkSize k L:ℝ))) →
      (∀a b,¬TransferBadArrangement (a⁻¹*b) → selectedCovariance C spectator s k a b≤
        Real.exp (-(frequencyBudget Bs BD Bz k L k+65*(2:ℝ)^k*(bulkSize k L:ℝ)))) →
      ‖decompositionAmplitude d C.favorable C.sources (frequencyBound Bs BD Bz k L)
        C.giant spectator C.scale C.giantCenter (bulkSize k L/2) s k C.bulkBin C.spectatorBin k‖^2 ≤
          Real.exp (-63*(2:ℝ)^k*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_final_upper_of_covariance_eventually d Bs BD Bz Ccov 18
      hBs hBD hBz (by norm_num) hk hrate,
    actualRegularEnergy_initial_eventually d Bs BD Bz (by omega : 0<k)]
    with L hupper hreg
  intro E C hGlo hGhi hclo hchi htb htd spectator s hbad hgood
  exact hupper E C spectator s
    (hreg E C hGlo hGhi hclo hchi htb htd _ spectator (2*s) k le_rfl) hbad hgood

end Ostmann.Conclusion

end

end OAI
