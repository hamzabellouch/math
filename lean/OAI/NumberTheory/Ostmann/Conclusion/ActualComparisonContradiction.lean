import OAI.NumberTheory.Ostmann.Conclusion.ActualFinalUpperRegular
import OAI.NumberTheory.Ostmann.Conclusion.ActualTransferLower

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open Construction Filter

theorem selected_comparisons_incompatible_eventually (d : Decomposition)
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
      Real.exp (-28*(bulkSize k L:ℝ))≤
        ‖decompositionAmplitude d C.favorable C.sources (frequencyBound Bs BD Bz k L)
          C.giant spectator C.scale C.giantCenter (bulkSize k L/2) s k C.bulkBin C.spectatorBin 0‖ →
      (∀j<k,extendedDiagonal d C.favorable C.sources (Template.initial (2*(bulkSize k L/2)) k)
          (frequencyBound Bs BD Bz k L) C.giant spectator (2*s) C.scale C.giantCenter
          (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin) j ≤
        Real.exp (-65*(2:ℝ)^j*(bulkSize k L:ℝ))) →
      (∀a b,TransferBadArrangement (a⁻¹*b) → selectedCovariance C spectator s k a b≤
        Real.exp ((2:ℝ)^k*(initialGap Bs k L+Ccov*(bulkSize k L:ℝ))+(bulkSize k L:ℝ))) →
      (∀a b,¬TransferBadArrangement (a⁻¹*b) → selectedCovariance C spectator s k a b≤
        Real.exp (-(frequencyBudget Bs BD Bz k L k+65*(2:ℝ)^k*(bulkSize k L:ℝ)))) → False := by
  filter_upwards [selected_final_upper_of_actual_covariance_eventually d Bs BD Bz Ccov
      hBs hBD hBz hk hrate,
    selected_amplitude_lower_of_diagonal_eventually d Bs BD Bz (by omega : 0<k),
    (bulkSize_tendsto_atTop (by omega : 0<k)).eventually_gt_atTop 0]
    with L hupper hlower hm
  intro E C hGlo hGhi hclo hchi htb htd spectator s hinit hdiag hbad hgood
  have hu := hupper E C hGlo hGhi hclo hchi htb htd spectator s hbad hgood
  have hl := hlower E C hGlo hGhi hclo hchi htb htd spectator s C.scale hinit hdiag k le_rfl
  have hsq := mul_self_le_mul_self (Real.exp_pos _).le hl
  have heq : Real.exp (-31*(2:ℝ)^k*(bulkSize k L:ℝ)) *
      Real.exp (-31*(2:ℝ)^k*(bulkSize k L:ℝ)) =
      Real.exp (-62*(2:ℝ)^k*(bulkSize k L:ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq,← sq] at hsq
  have hexp := Real.exp_le_exp.mp (hsq.trans hu)
  have hp : 0 < (2:ℝ)^k*(bulkSize k L:ℝ) := mul_pos (by positivity) hm
  nlinarith

end Ostmann.Conclusion

end

end OAI
