import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedWellMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarSobolev

namespace OAI

/-! The actual other-well residual has exponentially small L2 mass.
The square of a nonpositive bounded well is controlled by its negative
well matrix element, so the checked two-tail estimate applies directly. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedWellAction (freq : ℝ) (u w : PlanarPosition) (x : Position) : ℝ :=
  manufacturedPlanarWell ((positionSplitCoordinates x).1-w) * continuumLocalizedMode freq u x

theorem localizedWellAction_continuous (freq : ℝ) (u w : PlanarPosition) :
    Continuous (localizedWellAction freq u w) :=
  (manufacturedPlanarWell_C7.continuous.comp
    ((positionSplitCoordinates.continuous.fst).sub continuous_const)).mul
      (continuumLocalizedMode_C7 freq u).continuous

theorem localizedWellAction_memLp {freq : ℝ} (hfreq : 0 < freq) (u w : PlanarPosition) :
    MemLp (localizedWellAction freq u w) 2 := by
  apply (continuumLocalizedMode_memLp hfreq u).of_le_mul
    (c := PlanarSobolev.wellBound) (localizedWellAction_continuous freq u w).aestronglyMeasurable
  filter_upwards [] with x
  rw [localizedWellAction, norm_mul]
  exact mul_le_mul_of_nonneg_right (PlanarSobolev.wellBound_spec _) (norm_nonneg _)

theorem localizedWellAction_square_integrable {freq : ℝ} (hfreq : 0 < freq) (u w : PlanarPosition) :
    Integrable (fun x => localizedWellAction freq u w x ^ 2) :=
  (memLp_two_iff_integrable_sq (localizedWellAction_continuous freq u w).aestronglyMeasurable).mp
    (localizedWellAction_memLp hfreq u w)

theorem localizedWellAction_square_le_matrix {freq : ℝ} (hfreq : 0 < freq) (u w : PlanarPosition) :
    (∫ x, localizedWellAction freq u w x ^ 2) ≤ PlanarSobolev.wellBound * |planarWellMatrix u u w| := by
  have hp (x : Position) : localizedWellAction freq u w x ^ 2 ≤
      PlanarSobolev.wellBound * (-localizedWellIntegrand freq u u w x) := by
    have hn := manufacturedPlanarWell_nonpositive ((positionSplitCoordinates x).1-w)
    have hb := PlanarSobolev.wellBound_spec ((positionSplitCoordinates x).1-w)
    rw [Real.norm_eq_abs, abs_of_nonpos hn] at hb
    have hsq : manufacturedPlanarWell ((positionSplitCoordinates x).1-w)^2 ≤
        PlanarSobolev.wellBound * (-manufacturedPlanarWell ((positionSplitCoordinates x).1-w)) := by
      nlinarith [mul_nonneg (neg_nonneg.mpr hn) (sub_nonneg.mpr hb)]
    have h := mul_le_mul_of_nonneg_right hsq (sq_nonneg (continuumLocalizedMode freq u x))
    unfold localizedWellAction localizedWellIntegrand
    nlinarith only [h]
  have h := integral_mono (localizedWellAction_square_integrable hfreq u w)
    ((localizedWellIntegrand_integrable hfreq u u w).neg.const_mul PlanarSobolev.wellBound) hp
  simp only [Pi.neg_apply] at h
  rw [integral_const_mul, integral_neg, localizedWellIntegrand_integral hfreq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (neg_le_abs _) PlanarSobolev.wellBound_nonnegative)

theorem localizedWellAction_square_decay {freq D : ℝ} (hfreq : 0 < freq)
    (u w : PlanarPosition) (hd : D ≤ ‖u-w‖) :
    (∫ x, localizedWellAction freq u w x ^ 2) ≤
      (PlanarSobolev.wellBound * planarWellMatrixConstant) * Real.exp (-(19/10 : ℝ)*D) := by
  exact (localizedWellAction_square_le_matrix hfreq u w).trans
    ((mul_le_mul_of_nonneg_left (planarWellMatrix_two_far u u w hd hd)
      PlanarSobolev.wellBound_nonnegative).trans_eq (mul_assoc _ _ _).symm)

end ContinuumCoulomb

end

end OAI
