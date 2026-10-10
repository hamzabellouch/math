import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.SharpLocalPotentialBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma sharpPatchRemainder_nonneg {a b m : ℝ} (ha : 0 < a) (hb : 0 < b) (hm : 0 ≤ m) :
    0 ≤ sharpPatchRemainder a b m := by
  have hI := localizationIMSConstant_nonneg
  have hN := neumannRemainderConstant_pos.le
  have hP := packetDirichlet_nonneg canonicalRealPacket
  have hC : 0 ≤ actualCellMomentConstant := le_trans zero_le_one actualCellMomentConstant_one_le
  have hF : 0 ≤ sharpFreshFieldConstant := le_trans zero_le_one sharpFreshFieldConstant_one_le
  unfold sharpPatchRemainder
  positivity

lemma sharpLocalPotentialBudget_nonneg {a m u : ℝ} (ha : 0 < a) (_hm : 0 ≤ m)
    (hu : 0 ≤ u) : 0 ≤ sharpLocalPotentialBudget a m u := by
  have hC := sharpOrdinaryDensityConstant_nonneg
  unfold sharpLocalPotentialBudget
  positivity

lemma sharpPotentialRemainder_nonneg {a b m D q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 ≤ m) (hq : 0 < q) : 0 ≤ sharpPotentialRemainder a b m D q := by
  have hC : 0 ≤ actualCellMomentConstant := le_trans zero_le_one actualCellMomentConstant_one_le
  have hT := tfPatchDensityCapConstant_pos.le
  have hL1 := sharpLocalPotentialBudget_nonneg ha hm (by positivity : 0 ≤ q+Real.sqrt 3*b)
  have hL2 := sharpLocalPotentialBudget_nonneg ha hm (by positivity : 0 ≤ Real.sqrt 3*b)
  unfold sharpPotentialRemainder
  positivity

lemma sharpPatchRemainder_scale {a b m t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 ≤ m) (ht : 1 ≤ t) :
    sharpPatchRemainder a b (t*m) ≤ t^2*sharpPatchRemainder a b m := by
  let L := localizationIMSConstant/b^2*Real.sqrt (8*b/a)*actualCellMomentConstant+
    b⁻¹^2*neumannRemainderConstant*actualCellMomentConstant+
    (((2*Real.pi+1)/2)/b)*actualCellMomentConstant+
    ((packetDirichlet canonicalRealPacket/2)*b⁻¹^2)*(768*sharpFreshFieldConstant)
  let P := b⁻¹^2*neumannRemainderConstant*actualCellMomentConstant^(2/3:ℝ)
  let Q := sharpFreshFieldConstant/a*Real.sqrt (8*b/a)*actualCellMomentConstant
  have hI := localizationIMSConstant_nonneg
  have hN := neumannRemainderConstant_pos.le
  have hP := packetDirichlet_nonneg canonicalRealPacket
  have hC : 0 ≤ actualCellMomentConstant := le_trans zero_le_one actualCellMomentConstant_one_le
  have hF : 0 ≤ sharpFreshFieldConstant := le_trans zero_le_one sharpFreshFieldConstant_one_le
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hPP : 0 ≤ P := by dsimp [P]; positivity
  have he (v : ℝ) : sharpPatchRemainder a b v = L*v+P*v^(4/3:ℝ)+Q*v^2 := by
    dsimp [sharpPatchRemainder,L,P,Q]
    ring
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have htt : t ≤ t^2 := by nlinarith
  have htp : t^(4/3:ℝ) ≤ t^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (4/3:ℝ) ≤ 2)
  rw [he,he,Real.mul_rpow ht0 hm,mul_pow]
  calc
    _ ≤ L*(t^2*m)+P*(t^2*m^(4/3:ℝ))+Q*(t^2*m^2) := by
      gcongr
    _ = _ := by ring

lemma sharpLocalPotentialBudget_scale {a m u t : ℝ} (ha : 0 < a) (hm : 0 ≤ m)
    (hu : 0 ≤ u) (ht : 1 ≤ t) :
    sharpLocalPotentialBudget a (t*m) u ≤ t^2*sharpLocalPotentialBudget a m u := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hC := sharpOrdinaryDensityConstant_nonneg
  have he : sharpLocalPotentialBudget a (t*m) u =
      t^(6/5:ℝ)*sharpLocalPotentialBudget a m u := by
    unfold sharpLocalPotentialBudget
    rw [show sharpOrdinaryDensityConstant*(t*m)^2/a =
      t^2*(sharpOrdinaryDensityConstant*m^2/a) by ring,
      Real.mul_rpow (sq_nonneg t) (by positivity),←Real.rpow_natCast,←Real.rpow_mul ht0]
    norm_num
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (sharpLocalPotentialBudget_nonneg ha hm hu)
  rw [←Real.rpow_two]
  exact Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (6/5:ℝ) ≤ 2)

lemma localOffsetMass_scale {y : Space} {D t : ℝ}
    (ht : 1 ≤ t) : localOffsetMass (t^2*D) y ≤ t*localOffsetMass D y := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hM : 0 ≤ max (1/(localCellRadius y)^3) 1 :=
    le_trans zero_le_one (le_max_right _ _)
  unfold localOffsetMass
  rw [mul_assoc,Real.sqrt_mul (sq_nonneg t),Real.sqrt_sq ht0]
  nlinarith

lemma sharpPotentialRemainder_scale {a b m D q t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hm : 0 ≤ m) (hq : 0 < q) (ht : 1 ≤ t) :
    sharpPotentialRemainder a b (t*m) (t^2*D) q ≤
      t^2*sharpPotentialRemainder a b m D q := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have htt : t ≤ t^2 := by nlinarith
  have ht2 : 1 ≤ t^2 := by nlinarith
  have hC : 0 ≤ actualCellMomentConstant := le_trans zero_le_one actualCellMomentConstant_one_le
  have hT := tfPatchDensityCapConstant_pos.le
  have hpatch := sharpPatchRemainder_scale ha hb hm ht
  have hs : Real.sqrt ((2/q)*(t^2*D+sharpPatchRemainder a b (t*m))) ≤
      t^2*Real.sqrt ((2/q)*(D+sharpPatchRemainder a b m)) := by
    calc
      _ ≤ Real.sqrt ((2/q)*(t^2*D+t^2*sharpPatchRemainder a b m)) := by
        apply Real.sqrt_le_sqrt
        gcongr
      _ = t*Real.sqrt ((2/q)*(D+sharpPatchRemainder a b m)) := by
        rw [show (2/q)*(t^2*D+t^2*sharpPatchRemainder a b m) =
          t^2*((2/q)*(D+sharpPatchRemainder a b m)) by ring,
          Real.sqrt_mul (sq_nonneg t),Real.sqrt_sq ht0]
      _ ≤ _ := mul_le_mul_of_nonneg_right htt (Real.sqrt_nonneg _)
  have hL1 := sharpLocalPotentialBudget_scale ha hm (by positivity : 0 ≤ q+Real.sqrt 3*b) ht
  have hL2 := sharpLocalPotentialBudget_scale ha hm (by positivity : 0 ≤ Real.sqrt 3*b) ht
  have hc : 2*Real.pi*tfPatchDensityCapConstant*q^2/a^6 ≤
      t^2*(2*Real.pi*tfPatchDensityCapConstant*q^2/a^6) :=
    le_mul_of_one_le_left (by positivity) ht2
  have hl : (Real.sqrt (8*b/a)*actualCellMomentConstant*(t*m))/a ≤
      t^2*((Real.sqrt (8*b/a)*actualCellMomentConstant*m)/a) := by
    calc
      _ = t*((Real.sqrt (8*b/a)*actualCellMomentConstant*m)/a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right htt (by positivity)
  unfold sharpPotentialRemainder
  nlinarith only [hs,hL1,hL2,hc,hl]

end CoulombAtom

end

end OAI
