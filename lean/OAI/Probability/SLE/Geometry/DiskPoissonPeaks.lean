import OAI.Probability.SLE.Geometry.ConformalDiskExit
import Mathlib.Analysis.Complex.Poisson

namespace OAI

/-! Bounded positive holomorphic peak tests for excluding atoms at the
two exceptional points of the half-plane disk chart. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def diskPeak (a : ℂ) (r : ℝ) (z : ℂ) : ℂ := (a+(r:ℂ)*z)/(a-(r:ℂ)*z)

lemma diskPeak_denominator {a : ℂ} (ha : ‖a‖=1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : a-(r:ℂ)*z ≠ 0 := by
  have hb : ‖(r:ℂ)*z‖ ≤ r := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
    nlinarith
  have hnorm := norm_sub_norm_le a ((r:ℂ)*z)
  rw [ha] at hnorm
  exact norm_pos_iff.mp (by linarith)

lemma diskPeak_norm_bound {a : ℂ} (ha : ‖a‖=1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖diskPeak a r z‖ ≤ (1+r)/(1-r) := by
  have hb : ‖(r:ℂ)*z‖ ≤ r := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
    nlinarith
  have hd : 1-r ≤ ‖a-(r:ℂ)*z‖ := by
    have hh := norm_sub_norm_le a ((r:ℂ)*z)
    rw [ha] at hh
    linarith
  have hn : ‖a+(r:ℂ)*z‖ ≤ 1+r := (norm_add_le _ _).trans (by rw [ha]; linarith)
  rw [diskPeak,norm_div]
  exact div_le_div₀ (by positivity) hn (by linarith) hd

lemma diskPeak_re_nonnegative {a : ℂ} (ha : ‖a‖=1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : 0 ≤ (diskPeak a r z).re := by
  have hb : ‖(r:ℂ)*z‖ < 1 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
    nlinarith
  have he := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := (r:ℂ)*z)) a
  have he' : (diskPeak a r z).re=(1-‖(r:ℂ)*z‖^2)/‖a-(r:ℂ)*z‖^2 := by
    simpa only [poissonKernel,herglotzRieszKernel,Function.comp_apply,sub_zero,ha,one_pow,diskPeak] using he.symm
  rw [he']
  exact div_nonneg (by nlinarith [norm_nonneg ((r:ℂ)*z)]) (sq_nonneg _)

lemma diskPeak_differentiable {a : ℂ} (ha : ‖a‖=1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1) :
    DifferentiableOn ℂ (diskPeak a r) (ball 0 1) := by
  apply ((differentiableOn_id.const_mul (r:ℂ)).const_add a).div
    ((differentiableOn_id.const_mul (r:ℂ)).const_sub a)
  intro z hz
  exact diskPeak_denominator ha hr hr1 (mem_ball_zero_iff.mp hz).le

lemma diskPeak_continuousAt_boundary {a z : ℂ} (ha : ‖a‖=1) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r<1) (hz : ‖z‖ ≤ 1) : ContinuousAt (diskPeak a r) z :=
  (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).div
    (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
    (diskPeak_denominator ha hr hr1 hz)

lemma diskPeak_zero {a : ℂ} (ha : ‖a‖=1) (r : ℝ) : diskPeak a r 0=1 := by
  have ha0 : a≠0 := norm_ne_zero_iff.mp (ha ▸ one_ne_zero)
  simp [diskPeak,ha0]

lemma diskPeak_at_peak {a : ℂ} (ha : ‖a‖=1) (r : ℝ) :
    diskPeak a r a=(((1+r)/(1-r):ℝ):ℂ) := by
  have ha0 : a≠0 := norm_ne_zero_iff.mp (ha ▸ one_ne_zero)
  rw [diskPeak,show a+(r:ℂ)*a=a*(1+r) by ring,
    show a-(r:ℂ)*a=a*(1-r) by ring,mul_div_mul_left _ _ ha0]
  push_cast
  rfl

end SLEExactGauge

end

end OAI
