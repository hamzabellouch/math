import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedPairDerivativeBounds
open Construction Conclusion HistoryOccurrenceVariables HistoryPairSmoothXi HistorySymbolicEncoding
open HistorySelectedPairDerivativeCounts HistoryProductWindows

theorem selected_amplitude_bound (Bs BD Bz L : ℝ) {k l : ℕ} (hBs : 0 ≤ Bs)
    (hk : 0 < k) (hl : l ≤ k) :
    Real.exp ((nominalInheritedWidth k l+2)+nominalRemovedWidth k l)*
      Real.exp (-((2^l:ℕ):ℝ)*initialGap Bs k L+sourceXiConstant l k (2+2*(k:ℝ))) ≤
        Real.exp (selectedExponent Bs BD Bz k*((bulkSize k L:ℝ)+1)) := by
  have ha := source_amplitude_le hl (Construction.initialGap_nonneg Bs hBs hk L) (E:=2+2*(k:ℝ))
  have hw := Real.exp_le_exp.mpr (counterpartWidths_le hl)
  calc
    _ ≤ Real.exp (widthConstant k)*Real.exp (amplitudeConstant k (2+2*(k:ℝ))) :=
      mul_le_mul hw ha (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (widthConstant k+amplitudeConstant k (2+2*(k:ℝ))) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hp := pairExponent_pos k (2+2*(k:ℝ)) (countConstant k)
        (InitialSourceChoice.selectedCancellationConstant_pos Bs BD Bz k).le
      have hs : widthConstant k+amplitudeConstant k (2+2*(k:ℝ)) ≤ selectedExponent Bs BD Bz k := by
        unfold selectedExponent
        linarith [abs_nonneg (Real.log (countConstant k))]
      exact hs.trans (le_mul_of_one_le_right (selectedExponent_pos Bs BD Bz k).le
        (by have := Nat.cast_nonneg (bulkSize k L) (α:=ℝ); linarith))

theorem selected_bulk_corrected_bound {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (hBs : 0 ≤ Bs) (hk : 0 < k)
    (hm : 1 ≤ bulkSize k L) {l : ℕ} (hl : l ≤ k) (h g : History l)
    (hh : TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) h)
    (hg : TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) g)
    (j : ℕ) {cellCount : ℕ}
    (hc : cellCount ≤ (k+1)*countCoefficient k*(bulkSize k L/2+1)) :
    correctedPairDerivativeBound (nominalInheritedWidth k l+1) (nominalRemovedWidth k l)
      (pairedDiagonalHKeys h g j).length (pairedDiagonalUKeys h g j).length cellCount h g
      (frequencyBound Bs BD Bz k L) (bulkSize k L/2) k C.bulkBin
      (initialGap Bs k L) (2+2*(k:ℝ)) (C.cells.center (bulkSize k L/2)) ≤
      Real.exp (selectedExponent Bs BD Bz k*((bulkSize k L:ℝ)+1)) := by
  apply le_trans _ (selected_corrected_bound C hBs hk hm hl h g hh hg j hc)
  unfold correctedPairDerivativeBound
  apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
  positivity [pairDerivativeBound_nonneg h g (frequencyBound Bs BD Bz k L) (bulkSize k L/2)
    k C.bulkBin (initialGap Bs k L) (2+2*(k:ℝ)) (C.cells.center (bulkSize k L/2)),
    rootCounterpartDerivativeConstant_pos]

end Ostmann.Arithmetic.HistorySelectedPairDerivativeBounds

end

end OAI
