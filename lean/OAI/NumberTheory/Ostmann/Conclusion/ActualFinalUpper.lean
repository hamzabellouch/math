import OAI.NumberTheory.Ostmann.Conclusion.FinalRateAbsorption
import OAI.NumberTheory.Ostmann.Conclusion.SelectedPermutation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Conclusion
open Construction Filter

theorem selected_final_upper_of_covariance_eventually (d : Decomposition)
    (Bs BD Bz Ccov R0 : ℝ) (hBs : 0≤Bs) (hBD : 0≤BD) (hBz : 0≤Bz) (hR0 : 0<R0)
    {k : ℕ} (hk : 2≤k) (hrate : finalRate BD Bs Bz (Ccov+2) k < -66) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E)
      (spectator : PrimeSource)(s : ℕ),
      actualRegularEnergy C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) C.giant spectator (2*s)
        (residueTransform d) (favorableGiantResidueTransform d C.favorable) k ≤
          R0*(2*(frequencyBound Bs BD Bz k L k:ℝ)+1) →
      (∀a b,TransferBadArrangement (a⁻¹*b) → selectedCovariance C spectator s k a b≤
        Real.exp ((2:ℝ)^k*(initialGap Bs k L+Ccov*(bulkSize k L:ℝ))+(bulkSize k L:ℝ))) →
      (∀a b,¬TransferBadArrangement (a⁻¹*b) → selectedCovariance C spectator s k a b≤
        Real.exp (-(frequencyBudget Bs BD Bz k L k+65*(2:ℝ)^k*(bulkSize k L:ℝ)))) →
      ‖decompositionAmplitude d C.favorable C.sources (frequencyBound Bs BD Bz k L)
        C.giant spectator C.scale C.giantCenter (bulkSize k L/2) s k C.bulkBin C.spectatorBin k‖^2 ≤
          Real.exp (-63*(2:ℝ)^k*(bulkSize k L:ℝ)) := by
  have hnum := eventually_finalRate_absorption Bs BD Bz 31 R0 Ccov hBs hBD hBz hR0 hk
    (by norm_num; exact hrate)
  filter_upwards [hnum,(bulkSize_tendsto_atTop (by omega : 0<k)).eventually_gt_atTop 0]
    with L hnum hm
  intro E C spectator s hreg hbad hgood
  have hm' : 0<bulkSize k L := by exact_mod_cast hm
  have h := selectedAmplitude_sq_le_of_covariance C spectator s k hm'
    (Real.exp_pos _).le (Real.exp_pos _).le hreg hbad hgood
  have hnum' :
      R0*(2*(frequencyBound Bs BD Bz k L k:ℝ)+1)*
        (((2:ℝ)^k)^(2*(2^k))*Real.exp ((2-(3/4:ℝ)*Real.log ((2:ℝ)^k))*(2:ℝ)^k*(bulkSize k L:ℝ))*
          Real.exp ((2:ℝ)^k*(initialGap Bs k L+Ccov*(bulkSize k L:ℝ))+(bulkSize k L:ℝ))+
          Real.exp (-(frequencyBudget Bs BD Bz k L k+65*(2:ℝ)^k*(bulkSize k L:ℝ)))) ≤
        Real.exp (-63*(2:ℝ)^k*(bulkSize k L:ℝ)) := by
    norm_num only at hnum
    simpa only [neg_mul] using hnum
  refine le_trans ?_ hnum'
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using h

end Ostmann.Conclusion

end

end OAI
