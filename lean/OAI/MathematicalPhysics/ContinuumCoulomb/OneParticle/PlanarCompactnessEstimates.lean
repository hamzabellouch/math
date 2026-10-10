import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarProjectionGap

namespace OAI

/-! Compactness estimates for the actual manufactured planar well. They
reduce the positive gap to uniqueness of its attained ground vector. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.PlanarSobolev

local instance instPlanarCompactnessEstimatesMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instPlanarCompactnessEstimatesBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instPlanarCompactnessEstimatesMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

theorem shiftedForm_parallelogram (u v : Target) :
    shiftedForm (u+v)+shiftedForm (u-v) = 2*shiftedForm u+2*shiftedForm v := by
  have hp := shiftedForm_add_smul u v 1
  have hm := shiftedForm_add_smul u v (-1)
  simp only [one_smul,one_mul,one_pow] at hp
  simp only [neg_one_smul,neg_one_mul,neg_one_sq,one_mul] at hm
  rw [sub_eq_add_neg]
  linarith

theorem shiftedForm_sub_le (u v : Sobolev) :
    shiftedForm (u-v).val ≤ 2*shiftedForm u.val+2*shiftedForm v.val := by
  have he := shiftedForm_parallelogram u.val v.val
  have hn := shiftedForm_nonnegative (u+v)
  change 0 ≤ shiftedForm (u.val+v.val) at hn
  change shiftedForm (u.val-v.val) ≤ _
  linarith

theorem shiftedForm_controls_norm (u : Sobolev) :
    ‖u‖^2 ≤ 2*shiftedForm u.val +
      2*‖u.val.1‖*‖wellMultiplier u.val.1‖ := by
  have hi := (abs_le.mp (abs_real_inner_le_norm u.val.1 (wellMultiplier u.val.1))).1
  change (max ‖u.val.1‖ ‖u.val.2‖)^2 ≤ _
  unfold shiftedForm form
  rcases le_total ‖u.val.1‖ ‖u.val.2‖ with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖u.val.1‖]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg ‖u.val.2‖]

theorem nearGround_norm_bound (u : Sobolev) (hm : ‖u.val.1‖ ≤ 1)
    (hs : shiftedForm u.val ≤ 1) : ‖u‖ ≤ 3+2*‖wellMultiplier‖ := by
  have he := shiftedForm_controls_norm u
  have hw := wellMultiplier.le_opNorm u.val.1
  have hW := norm_nonneg wellMultiplier
  have hmul : ‖u.val.1‖*‖wellMultiplier u.val.1‖ ≤ ‖wellMultiplier‖ := by
    calc
      _ ≤ 1*(‖wellMultiplier‖*1) := mul_le_mul hm
        (hw.trans (mul_le_mul_of_nonneg_left hm hW)) (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith [norm_nonneg u,sq_nonneg ‖wellMultiplier‖]

theorem nearGround_distance_bound (u v : Sobolev)
    (hu : ‖u.val.1‖ ≤ 1) (hv : ‖v.val.1‖ ≤ 1) :
    dist u v ^ 2 ≤ 4*shiftedForm u.val+4*shiftedForm v.val+
      4*dist (wellMultiplier u.val.1) (wellMultiplier v.val.1) := by
  have hs := shiftedForm_controls_norm (u-v)
  have hd := shiftedForm_sub_le u v
  have hm : ‖(u-v).val.1‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hm (norm_nonneg (wellMultiplier (u-v).val.1))
  rw [dist_eq_norm,dist_eq_norm,← map_sub]
  change ‖u-v‖^2 ≤ _
  change ‖u-v‖^2 ≤ 2*shiftedForm (u-v).val+
    2*‖u.val.1-v.val.1‖*‖wellMultiplier (u.val.1-v.val.1)‖ at hs
  change shiftedForm (u-v).val ≤ _ at hd
  change ‖u.val.1-v.val.1‖*‖wellMultiplier (u.val.1-v.val.1)‖ ≤
    2*‖wellMultiplier (u.val.1-v.val.1)‖ at hmul
  linarith

end ContinuumCoulomb.PlanarSobolev

end

end OAI
