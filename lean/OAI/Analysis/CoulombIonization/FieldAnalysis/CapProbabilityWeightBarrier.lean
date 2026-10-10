import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.SharpBudgetMonotoneBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.CapBudgetHomogeneityBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis

def physicalFieldCapBudget (D : ℝ) (y : Space) (b q u : ℝ) : ℝ :=
  tfPatchCapConstant/(localCellRadius y)^4+
    (sharpPotentialRemainder (localCellRadius y) b (localOffsetMass D y) D q+
      sharpLocalPotentialBudget (localCellRadius y) (localOffsetMass D y) u)

lemma physicalFieldCapBudget_scale {y : Space} (hy : y ≠ 0) {b q u D t : ℝ}
    (hb : 0 < b) (hq : 0 < q) (hu : 0 ≤ u) (ht : 1 ≤ t) :
    physicalFieldCapBudget (t^2*D) y b q u ≤ t^2*physicalFieldCapBudget D y b q u := by
  have ha := localCellRadius_pos hy
  have hm : 0 ≤ localOffsetMass D y := le_trans zero_le_one (localOffsetMass_one_le _ _)
  have hm' : 0 ≤ localOffsetMass (t^2*D) y :=
    le_trans zero_le_one (localOffsetMass_one_le _ _)
  have hM := localOffsetMass_scale (y := y) (D := D) ht
  have hS := sharpPotentialRemainder_mono (D := t^2*D) ha hb hm' hM le_rfl hq
  have hL := sharpLocalPotentialBudget_mono ha hm' hM hu le_rfl
  have hPS := sharpPotentialRemainder_scale (D := D) ha hb hm hq ht
  have hLS := sharpLocalPotentialBudget_scale ha hm hu ht
  have hC := tfPatchCapConstant_pos.le
  have ht2 : 1 ≤ t^2 := by nlinarith
  have hcap : tfPatchCapConstant/(localCellRadius y)^4 ≤
      t^2*(tfPatchCapConstant/(localCellRadius y)^4) :=
    le_mul_of_one_le_left (by positivity) ht2
  unfold physicalFieldCapBudget
  nlinarith only [hS,hL,hPS,hLS,hcap]

lemma probability_weighted_cap {y : Space} (hy : y ≠ 0) {b q u D p : ℝ}
    (hb : 0 < b) (hq : 0 < q) (hu : 0 ≤ u) (hp : 0 < p) (hp1 : p ≤ 1) :
    p*physicalFieldCapBudget D y b q u ≤
      p^(3/4:ℝ)*physicalFieldCapBudget (p^(1/4:ℝ)*D) y b q u := by
  have ht : 1 ≤ p^(-(1/8):ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hp hp1 (by norm_num)
  have he : (p^(-(1/8):ℝ))^2*p^(1/4:ℝ) = 1 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hp.le,←Real.rpow_add hp]
    norm_num
  have h := physicalFieldCapBudget_scale (D := p^(1/4:ℝ)*D) hy hb hq hu ht
  rw [←mul_assoc,he,one_mul] at h
  have hh := mul_le_mul_of_nonneg_left h hp.le
  have he' : p*(p^(-(1/8):ℝ))^2 = p^(3/4:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hp.le]
    calc p*p^(-(1/8)*2:ℝ) = p^(1:ℝ)*p^(-(1/8)*2:ℝ) := by rw [Real.rpow_one]
         _ = _ := by rw [←Real.rpow_add hp]; norm_num
  simpa only [←mul_assoc,he'] using hh

end CoulombAtom

end

end OAI
