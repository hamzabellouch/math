import OAI.NumberTheory.Ostmann.Conclusion.TransferRecurrence
import OAI.NumberTheory.Ostmann.Construction.GiantNormalizationReserve
import OAI.NumberTheory.Ostmann.Construction.SelectedTransferEventually

namespace OAI

open Erdos970

noncomputable section
open Filter
namespace Ostmann.Conclusion
open Construction

theorem selected_amplitude_lower_of_diagonal_eventually (d : Decomposition)
    (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀(spectator : PrimeSource)(s : ℕ)(X : ℝ),
      Real.exp (-28*(bulkSize k L:ℝ))≤
        ‖decompositionAmplitude d C.favorable C.sources (frequencyBound Bs BD Bz k L)
          C.giant spectator X C.giantCenter (bulkSize k L/2) s k C.bulkBin C.spectatorBin 0‖ →
      (∀j<k,extendedDiagonal d C.favorable C.sources (Template.initial (2*(bulkSize k L/2)) k)
          (frequencyBound Bs BD Bz k L) C.giant spectator (2*s) X C.giantCenter
          (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin) j ≤
        Real.exp (-65*(2:ℝ)^j*(bulkSize k L:ℝ))) →
      ∀j≤k,Real.exp (-31*(2:ℝ)^j*(bulkSize k L:ℝ))≤
        ‖decompositionAmplitude d C.favorable C.sources (frequencyBound Bs BD Bz k L)
          C.giant spectator X C.giantCenter (bulkSize k L/2) s k C.bulkBin C.spectatorBin j‖ := by
  filter_upwards [selected_transfer_eventually d Bs BD Bz hk,
    initial_giant_normalization_reserve_eventually d Bs BD Bz hk,
    (bulkSize_tendsto_atTop hk).eventually_gt_atTop 0] with L htrans hcost hm
  intro E C hG hGu hcl hcu hb hd spectator s X hinit hdiag
  let η := fun j => ‖decompositionAmplitude d C.favorable C.sources (frequencyBound Bs BD Bz k L)
    C.giant spectator X C.giantCenter (bulkSize k L/2) s k C.bulkBin C.spectatorBin j‖
  let D := fun j => extendedDiagonal d C.favorable C.sources (Template.initial (2*(bulkSize k L/2)) k)
    (frequencyBound Bs BD Bz k L) C.giant spectator (2*s) X C.giantCenter
    (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin) j
  have hc := hcost E C hG hGu hcl hcu
  have hi : Real.exp (-28*(bulkSize k L:ℝ))≤|η 0| := by
    simpa only [η,abs_of_nonneg (norm_nonneg _)] using hinit
  have hd' : ∀j<k,D j≤Real.exp (-(2*(28+3)+3)*(2:ℝ)^j*(bulkSize k L:ℝ)) := by
    norm_num
    intro j hj
    simpa only [D,neg_mul] using hdiag j hj
  have ht : ∀j<k,Real.exp (-giantNormalizationCost C.giantCenter)*|η j|^2≤D j+|η (j+1)| := by
    intro j hj
    have h := htrans E C hG hcl hcu hb hd spectator s X j hj
    simpa only [exp_logCellMass_eq_exp_neg_giantNormalizationCost,η,D,
      abs_of_nonneg (norm_nonneg _)] using h
  have hiter := transfer_exact_lower η D 28 (bulkSize k L) (giantNormalizationCost C.giantCenter)
    hm hc k hi hd' ht
  intro j hj
  have hbudget := transferBudget_lt 28 (bulkSize k L) (giantNormalizationCost C.giantCenter) hm hc j
  have hlow := hiter j hj
  have hexp : Real.exp (-31*(2:ℝ)^j*(bulkSize k L:ℝ)) ≤
      Real.exp (-transferBudget 28 (bulkSize k L) (giantNormalizationCost C.giantCenter) j) := by
    apply Real.exp_le_exp.mpr
    norm_num at hbudget
    linarith
  simpa only [η,abs_of_nonneg (norm_nonneg _)] using hexp.trans hlow

end Ostmann.Conclusion

end

end OAI
