import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.SharpLocalPotentialBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma sharpPatchRemainder_mono {a b m n : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 ≤ m) (hmn : m ≤ n) : sharpPatchRemainder a b m ≤ sharpPatchRemainder a b n := by
  have hI := localizationIMSConstant_nonneg
  have hN := neumannRemainderConstant_pos.le
  have hP := packetDirichlet_nonneg canonicalRealPacket
  have hC : 0 ≤ actualCellMomentConstant := le_trans zero_le_one actualCellMomentConstant_one_le
  have hF : 0 ≤ sharpFreshFieldConstant := le_trans zero_le_one sharpFreshFieldConstant_one_le
  have hn : 0 ≤ n := hm.trans hmn
  unfold sharpPatchRemainder
  gcongr

lemma sharpLocalPotentialBudget_mono {a m n u v : ℝ} (ha : 0 < a)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hu : 0 ≤ u) (huv : u ≤ v) :
    sharpLocalPotentialBudget a m u ≤ sharpLocalPotentialBudget a n v := by
  have hC : 0 ≤ sharpOrdinaryDensityConstant := sharpOrdinaryDensityConstant_nonneg
  unfold sharpLocalPotentialBudget
  gcongr

lemma sharpPotentialRemainder_mono {a b m n D E q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hDE : D ≤ E) (hq : 0 < q) :
    sharpPotentialRemainder a b m D q ≤ sharpPotentialRemainder a b n E q := by
  have hC : 0 ≤ actualCellMomentConstant := le_trans zero_le_one actualCellMomentConstant_one_le
  unfold sharpPotentialRemainder
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · apply add_le_add
        · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
            (add_le_add hDE (sharpPatchRemainder_mono ha hb hm hmn)) (by positivity))
        · exact sharpLocalPotentialBudget_mono ha hm hmn (by positivity) le_rfl
      · exact le_rfl
    · exact sharpLocalPotentialBudget_mono ha hm hmn (by positivity) le_rfl
  · gcongr

lemma sharp_combined_error_mono {y : Space} (hy : y ≠ 0) {b q D E u : ℝ}
    (hb : 0 < b) (hq : 0 < q) (hDE : D ≤ E) (hu : 0 ≤ u) :
    sharpPotentialRemainder (localCellRadius y) b (localOffsetMass D y) D q+
      sharpLocalPotentialBudget (localCellRadius y) (localOffsetMass D y) u ≤
    sharpPotentialRemainder (localCellRadius y) b (localOffsetMass E y) E q+
      sharpLocalPotentialBudget (localCellRadius y) (localOffsetMass E y) u := by
  have hm := localOffsetMass_mono hDE y
  have hn : 0 ≤ localOffsetMass D y := le_trans zero_le_one (localOffsetMass_one_le D y)
  exact add_le_add (sharpPotentialRemainder_mono (localCellRadius_pos hy) hb hn hm hDE hq)
    (sharpLocalPotentialBudget_mono (localCellRadius_pos hy) hn hm hu le_rfl)

end CoulombAtom

end

end OAI
