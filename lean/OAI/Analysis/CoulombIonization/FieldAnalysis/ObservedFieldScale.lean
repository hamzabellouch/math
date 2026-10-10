import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.AnnularCutExcess
import OAI.Analysis.CoulombIonization.FieldAnalysis.InnerCapStatistic
import OAI.Analysis.CoulombIonization.RadialBounds.CoulombTailNumerics

namespace OAI

open MeasureTheory Set Metric
noncomputable section
namespace CoulombAtom

def innerScale (D h : ℝ) : ℝ := 1/h^8+1/h^2+D/h
lemma innerScale_nonneg {D h : ℝ} (hD : 0 ≤ D) (hh : 0 < h) : 0 ≤ innerScale D h := by
  unfold innerScale; positivity

lemma annularOffsetMass_sq_div {D h : ℝ} (hD : 0 ≤ D) (hh : 0 < h) :
    (annularOffsetMass D h)^2/h^2 ≤ 3*innerScale D h := by
  calc
    _ ≤ (3*(1/h^6+1+D*h))/h^2 := div_le_div_of_nonneg_right (annularOffsetMass_sq_le hD hh) (sq_nonneg _)
    _ = _ := by unfold innerScale; field_simp

lemma annularInnerRadiusScale {D h : ℝ} (hD : 0 ≤ D) (hh : 0 < h)
    {z : Space} (hz : z ∈ innerFieldTestAnnulus h) :
    (localOffsetMass D z/localCellRadius z)^2 ≤
      3*(annularCellScaleConstant 1 3*100000)^2*innerScale D h := by
  have hn := localOffsetMass_annular_bound_norm (alpha := 1) (beta := 3)
    (by norm_num) hh hD (by simpa only [one_mul] using hz.1) hz.2
  have ha : 0 < localCellRadius z := localCellRadius_pos (norm_pos_iff.mp (hh.trans_le hz.1))
  have har : h/100000 ≤ localCellRadius z := by unfold localCellRadius; linarith [hz.1]
  have hc := annularCellScaleConstant_one_le (1:ℝ) 3
  have hs := annularOffsetMass_one_le D h
  calc
    _ ≤ ((annularCellScaleConstant 1 3*annularOffsetMass D h)/(h/100000))^2 := by
      apply pow_le_pow_left₀ (div_nonneg (zero_le_one.trans (localOffsetMass_one_le D z)) ha.le)
      exact (div_le_div_of_nonneg_right hn ha.le).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) har)
    _ = (annularCellScaleConstant 1 3*100000)^2*((annularOffsetMass D h)^2/h^2) := by ring
    _ ≤ (annularCellScaleConstant 1 3*100000)^2*(3*innerScale D h) :=
      mul_le_mul_of_nonneg_left (annularOffsetMass_sq_div hD hh) (sq_nonneg _)
    _ = _ := by ring

lemma ensemble_field_annular_bound (E : CoreObservationEnsemble) {Z lam D h A : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hD : 0 ≤ D) (hh : 0 < h) (hm : E.mass = 1)
    (he : max (E.excess Z lam) 0/h ≤ A*innerScale D h)
    (hb : ∀ z ∈ innerFieldTestAnnulus h,
      E.countMoment z (8*localCellRadius z) ≤ actualCellMomentConstant*(localOffsetMass D z)^2)
    {z : Space} (hz : z ∈ innerFieldTestAnnulus h) :
    E.fieldMoment Z lam z ≤ localFieldUniversalConstant*
      (100000*A+(5+actualCellMomentConstant)*3*(annularCellScaleConstant 1 3*100000)^2)*innerScale D h := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hh.trans_le hz.1)
  have ha := localCellRadius_pos hz0
  have hr : h/100000 ≤ localCellRadius z := by unfold localCellRadius; linarith [hz.1]
  have hd : max (E.excess Z lam) 0/localCellRadius z ≤ 100000*A*innerScale D h := by
    calc
      _ ≤ max (E.excess Z lam) 0/(h/100000) := div_le_div_of_nonneg_left (le_max_right _ _) (by positivity) hr
      _ = 100000*(max (E.excess Z lam) 0/h) := by ring
      _ ≤ 100000*(A*innerScale D h) := mul_le_mul_of_nonneg_left he (by norm_num)
      _ = _ := by ring
  have hf := ensemble_local_field_scale E z ha
    (show 12*localCellRadius z ≤ ‖z‖ by unfold localCellRadius; nlinarith [norm_nonneg z]) hm hZ hlam
  have hs := localFieldScale_linear_bound (D := max (E.excess Z lam) 0) ha (localOffsetMass_one_le D z)
    (localOffsetMass_cube_le D z) actualCellMomentConstant_one_le (hb z hz)
  have hc : 0 ≤ 5+actualCellMomentConstant := by have := actualCellMomentConstant_one_le; linarith
  calc
    _ ≤ localFieldUniversalConstant*(max (E.excess Z lam) 0/localCellRadius z+
        (5+actualCellMomentConstant)*(localOffsetMass D z/localCellRadius z)^2) :=
      hf.trans (mul_le_mul_of_nonneg_left hs localFieldUniversalConstant_pos.le)
    _ ≤ localFieldUniversalConstant*(100000*A*innerScale D h+
        (5+actualCellMomentConstant)*(3*(annularCellScaleConstant 1 3*100000)^2*innerScale D h)) :=
      mul_le_mul_of_nonneg_left (add_le_add hd (mul_le_mul_of_nonneg_left
        (annularInnerRadiusScale hD hh hz) hc)) localFieldUniversalConstant_pos.le
    _ = _ := by ring

lemma innerFieldVolume_le {h : ℝ} (hh : 0 < h) : innerFieldVolume h ≤ 36*Real.pi*h^3 := by
  have hs : innerFieldTestAnnulus h ⊆ closedBall (0:Space) (3*h) := by
    intro z hz
    simpa only [mem_closedBall,dist_zero_right] using hz.2
  have hv := measureReal_mono (μ := (volume : Measure Space)) hs (isCompact_closedBall (0:Space) (3*h)).measure_ne_top
  rw [space_closedBall_real (0:Space) (by positivity : 0 ≤ 3*h)] at hv
  unfold innerFieldVolume
  nlinarith only [hv]

lemma innerCapAverage_scale (E : CoreObservationEnsemble) {Z lam D h A T : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hD : 0 ≤ D) (hh : 0 < h) (hm : E.mass = 1)
    (hA : 0 ≤ A)
    (hf : ∀ z ∈ innerFieldTestAnnulus h, E.fieldMoment Z lam z ≤ A*innerScale D h)
    (ht : E.weightedMoment (coulombTailWeight h) ≤ T*innerScale D h) :
    E.innerCapAverage Z lam h ≤
      (3*(packetDensityConstant*64*(36*Real.pi))^2*A+3*(16*packetPotentialConstant)^2*T)*innerScale D h+3*lam^2 := by
  have hb := E.innerCapAverage_bound hZ hlam hh hm hf ht
  have hv := innerFieldVolume_le hh
  have hv0 := innerFieldVolume_nonneg h
  have hcoef : (packetDensityConstant/(h/4)^3)^2*(innerFieldVolume h)^2 ≤
      (packetDensityConstant*64*(36*Real.pi))^2 := by
    calc
      _ ≤ (packetDensityConstant/(h/4)^3)^2*(36*Real.pi*h^3)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv0 hv 2) (sq_nonneg _)
      _ = _ := by field_simp; ring
  have hc := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hA (innerScale_nonneg hD hh))
  nlinarith only [hb,hc]

end CoulombAtom

end

end OAI
