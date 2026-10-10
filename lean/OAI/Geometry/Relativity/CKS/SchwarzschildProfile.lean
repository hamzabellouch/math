import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.TailSymbols

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace CKSSchwarzschild

lemma velocity_smooth (m : ℝ) : ContDiff ℝ ∞ (velocity m) := by
  unfold velocity
  exact contDiff_const.add ((contDiff_id.add contDiff_const).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).sub contDiff_const)))
lemma velocity_near (m r : ℝ) (hr : r ≤ 2*m+1) : velocity m r = -1 := by
  simp [velocity,Real.smoothTransition.zero_of_nonpos (by linarith : r-2*m-1 ≤ 0)]
lemma velocity_far (m r : ℝ) (hr : 2*m+2 ≤ r) : velocity m r = r := by
  rw [velocity,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ r-2*m-1)]
  ring
lemma lapseSquared_pos {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) : 0 < lapseSquared m r := by
  have hrp : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) hm) hr
  rcases eq_or_lt_of_le hr with he|he
  · have hv := velocity_near m r (by linarith)
    have hm0 : m ≠ 0 := ne_of_gt hm
    subst r
    simp [lapseSquared,hv,hm0]
  · have hh : 2*m/r < 1 := (div_lt_one hrp).mpr he
    have hsq := sq_nonneg (velocity m r)
    unfold lapseSquared
    linarith
lemma lapseSquared_horizon {m : ℝ} (hm : 0 < m) : lapseSquared m (2*m) = 1 := by
  rw [lapseSquared,velocity_near m (2*m) (by linarith)]
  have hm0 : m ≠ 0 := ne_of_gt hm
  field_simp
  ring
lemma lapse_horizon {m : ℝ} (hm : 0 < m) : lapse m (2*m) = 1 := by
  rw [lapse,lapseSquared_horizon hm,Real.sqrt_one]
lemma lapseSquared_smoothAt {m r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ∞ (lapseSquared m) r := by
  exact (contDiffAt_const.sub (contDiffAt_const.div contDiffAt_id (ne_of_gt hr))).add
    ((velocity_smooth m).contDiffAt.pow 2)
lemma lapse_smoothAt {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) : ContDiffAt ℝ ∞ (lapse m) r := by
  exact (lapseSquared_smoothAt (lt_of_lt_of_le (mul_pos (by norm_num) hm) hr)).sqrt
    (ne_of_gt (lapseSquared_pos hm hr))
lemma lapse_pos {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) : 0 < lapse m r :=
  Real.sqrt_pos.mpr (lapseSquared_pos hm hr)
lemma lapse_sq {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) : (lapse m r)^2 = lapseSquared m r :=
  Real.sq_sqrt (lapseSquared_pos hm hr).le
lemma lapse_dominates_velocity {m r : ℝ} (hm : 0 < m) (hr : 2*m < r) :
    |velocity m r| < lapse m r := by
  have hrp : 0 < r := lt_trans (mul_pos (by norm_num) hm) hr
  have hh : 2*m/r < 1 := (div_lt_one hrp).mpr hr
  have hs := lapse_sq hm hr.le
  have hp := lapse_pos hm hr.le
  have hvs : (|velocity m r|)^2 = (velocity m r)^2 := sq_abs _
  unfold lapseSquared at hs
  nlinarith [abs_nonneg (velocity m r)]

end CKSSchwarzschild

end

end OAI
