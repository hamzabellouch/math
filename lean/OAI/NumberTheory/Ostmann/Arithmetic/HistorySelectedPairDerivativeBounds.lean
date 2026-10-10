import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedCancellationBound
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeBoundsCounts
import OAI.NumberTheory.Ostmann.Construction.LevelZeroFrequencyReserve

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedPairDerivativeBounds
open Construction Conclusion HistoryOccurrenceVariables HistoryPairSmoothXi HistorySymbolicEncoding
open HistorySelectedPairDerivativeCounts HistoryProductWindows Filter
open scoped BigOperators

def widthConstant (k : ℕ) : ℝ := 3+(2:ℝ)^k*(18+10*(k:ℝ))

lemma widthConstant_pos (k : ℕ) : 0 < widthConstant k := by unfold widthConstant; positivity

def selectedExponent (Bs BD Bz : ℝ) (k : ℕ) : ℝ :=
  widthConstant k+pairExponent k (2+2*(k:ℝ))
    (InitialSourceChoice.selectedCancellationConstant Bs BD Bz k) (countConstant k)+
    (|Real.log (countConstant k)|+1+amplitudeConstant k (2+2*(k:ℝ)))+1

lemma selectedExponent_pos (Bs BD Bz : ℝ) (k : ℕ) : 0 < selectedExponent Bs BD Bz k := by
  have := widthConstant_pos k
  have := pairExponent_pos k (2+2*(k:ℝ)) (countConstant k)
    (InitialSourceChoice.selectedCancellationConstant_pos Bs BD Bz k).le
  have := amplitudeConstant_nonneg k (2+2*(k:ℝ))
  unfold selectedExponent
  positivity

theorem selected_pair_bound {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (hBs : 0 ≤ Bs) (hk : 0 < k)
    (hm : 1 ≤ bulkSize k L) {l : ℕ} (hl : l ≤ k) (h g : History l)
    (hh : TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) h)
    (hg : TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) g) :
    pairDerivativeBound h g (frequencyBound Bs BD Bz k L) (bulkSize k L/2) k C.bulkBin
      (initialGap Bs k L) (2+2*(k:ℝ)) (C.cells.center (bulkSize k L/2)) ≤
      Real.exp (selectedExponent Bs BD Bz k*((bulkSize k L:ℝ)+1)) := by
  have hb : ((bulkSize k L/2:ℕ):ℝ) ≤ bulkSize k L := by exact_mod_cast Nat.div_le_self (bulkSize k L) 2
  have hn := pairDerivativeBound_le_exp (E:=2+2*(k:ℝ))
    (C.cells.center (bulkSize k L/2)) h g hl (Construction.initialGap_nonneg Bs hBs hk L)
    (InitialSourceChoice.selectedCancellationConstant_pos Bs BD Bz k).le (countConstant_pos k)
    (by exact_mod_cast hm) hb (C.selected_sourceCancellationBound_le_exp_linear hm hl)
    (actual_pair_card_bound hh hg hl hb)
  apply hn.trans (Real.exp_le_exp.mpr _)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have := widthConstant_pos k
  have := amplitudeConstant_nonneg k (2+2*(k:ℝ))
  unfold selectedExponent
  linarith [abs_nonneg (Real.log (countConstant k))]

theorem selected_corrected_bound {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (hBs : 0 ≤ Bs) (hk : 0 < k)
    (hm : 1 ≤ bulkSize k L) {l : ℕ} (hl : l ≤ k) (h g : History l)
    (hh : TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) h)
    (hg : TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) g)
    (j : ℕ) {cellCount : ℕ}
    (hc : cellCount ≤ (k+1)*countCoefficient k*(bulkSize k L/2+1)) :
    correctedPairDerivativeBound (nominalInheritedWidth k l+2) (nominalRemovedWidth k l)
      (pairedDiagonalHKeys h g j).length (pairedDiagonalUKeys h g j).length cellCount h g
      (frequencyBound Bs BD Bz k L) (bulkSize k L/2) k C.bulkBin
      (initialGap Bs k L) (2+2*(k:ℝ)) (C.cells.center (bulkSize k L/2)) ≤
      Real.exp (selectedExponent Bs BD Bz k*((bulkSize k L:ℝ)+1)) := by
  have hb : ((bulkSize k L/2:ℕ):ℝ) ≤ bulkSize k L := by exact_mod_cast Nat.div_le_self (bulkSize k L) 2
  exact correctedPairDerivativeBound_le_exp (E:=2+2*(k:ℝ))
    (C.cells.center (bulkSize k L/2)) h g hl (Construction.initialGap_nonneg Bs hBs hk L)
    (InitialSourceChoice.selectedCancellationConstant_pos Bs BD Bz k).le (countConstant_pos k)
    (widthConstant_pos k).le (by exact_mod_cast hm) hb
    (C.selected_sourceCancellationBound_le_exp_linear hm hl) (actual_pair_card_bound hh hg hl hb)
    ((counterpartWidths_le hl).trans (le_mul_of_one_le_right (widthConstant_pos k).le (by have := Nat.cast_nonneg (bulkSize k L) (α:=ℝ); linarith)))
    (actual_counterpart_count_bound h hg hl j hc hb)

theorem selected_bounds_eventually (d : Decomposition) (Bs BD Bz : ℝ) (hBs : 0 ≤ Bs)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      ∀ l ≤ k, ∀ (h g : History l),
      TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) h →
      TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) g → ∀ j : ℕ,
      pairDerivativeBound h g (frequencyBound Bs BD Bz k L) (bulkSize k L/2) k C.bulkBin
        (initialGap Bs k L) (2+2*(k:ℝ)) (C.cells.center (bulkSize k L/2)) ≤
        Real.exp (selectedExponent Bs BD Bz k*((bulkSize k L:ℝ)+1)) ∧
      correctedPairDerivativeBound (nominalInheritedWidth k l+2) (nominalRemovedWidth k l)
        (pairedDiagonalHKeys h g j).length (pairedDiagonalUKeys h g j).length
        ((∑ t : Fin (l+1), (diagonalCellKeys g t.val).length)+2) h g
        (frequencyBound Bs BD Bz k L) (bulkSize k L/2) k C.bulkBin
        (initialGap Bs k L) (2+2*(k:ℝ)) (C.cells.center (bulkSize k L/2)) ≤
        Real.exp (selectedExponent Bs BD Bz k*((bulkSize k L:ℝ)+1)) := by
  filter_upwards [(bulkSize_tendsto_atTop hk).eventually_ge_atTop (1:ℝ)] with L hL
  intro E C l hl h g hh hg j
  have hm : 1 ≤ bulkSize k L := by exact_mod_cast hL
  exact ⟨selected_pair_bound C hBs hk hm hl h g hh hg,
    selected_corrected_bound C hBs hk hm hl h g hh hg j (all_level_cells_add_two_le hg hl)⟩

end Ostmann.Arithmetic.HistorySelectedPairDerivativeBounds

end

end OAI
