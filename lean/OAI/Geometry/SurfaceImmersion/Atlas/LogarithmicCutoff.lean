import OAI.Geometry.SurfaceImmersion.Correction.SmoothTransitionDerivativeBound
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace OAI

/-! A compact cutoff constant near zero, with arbitrarily slow variation
 in the logarithm of the transverse distance. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

def logarithmicCutoff (L x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.smoothTransition (-Real.log x/L)

lemma logarithmicCutoff_one {L x : ℝ} (hL : 0 < L) (hx : |x| < Real.exp (-L)) :
    logarithmicCutoff L x = 1 := by
  by_cases hz : x = 0
  · simp [logarithmicCutoff,hz]
  · have hlog : Real.log x < -L := by
      rw [← Real.log_abs]
      exact (Real.log_lt_iff_lt_exp (abs_pos.mpr hz)).mpr hx
    rw [logarithmicCutoff,ite_eq_right hz]
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ hL).mpr
    linarith

lemma logarithmicCutoff_zero {L x : ℝ} (hL : 0 < L) (hx : 1 ≤ |x|) :
    logarithmicCutoff L x = 0 := by
  have hz : x ≠ 0 := by intro h; norm_num [h] at hx
  have hlog : 0 ≤ Real.log x := by
    rw [← Real.log_abs]
    exact Real.log_nonneg hx
  rw [logarithmicCutoff,ite_eq_right hz]
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) hL.le

lemma logarithmicCutoff_germ {L : ℝ} (hL : 0 < L) :
    logarithmicCutoff L =ᶠ[𝓝 (0:ℝ)] fun _ => 1 := by
  filter_upwards [ball_mem_nhds (0:ℝ) (Real.exp_pos (-L))] with x hx
  apply logarithmicCutoff_one hL
  simpa only [mem_ball,Real.dist_eq,sub_zero] using hx

lemma logarithmicCutoff_formula {L x : ℝ} (hx : x ≠ 0) :
    logarithmicCutoff L =ᶠ[𝓝 x] fun y => Real.smoothTransition (-Real.log y/L) := by
  filter_upwards [isOpen_ne.mem_nhds hx] with y hy
  exact ite_eq_right hy

lemma logarithmicCutoff_smooth {L : ℝ} (hL : 0 < L) :
    ContDiff ℝ ∞ (logarithmicCutoff L) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact contDiffAt_const.congr_of_eventuallyEq (logarithmicCutoff_germ hL)
  · have hc : ContDiffAt ℝ ∞ (fun y => Real.smoothTransition (-Real.log y/L)) x :=
      Real.smoothTransition.contDiff.contDiffAt.comp x ((Real.contDiffAt_log.mpr hx).neg.div_const L)
    exact hc.congr_of_eventuallyEq (logarithmicCutoff_formula hx)

lemma logarithmicCutoff_range (L x : ℝ) :
    0 ≤ logarithmicCutoff L x ∧ logarithmicCutoff L x ≤ 1 := by
  by_cases hx : x = 0
  · simp [logarithmicCutoff,hx]
  · exact ⟨by simpa only [logarithmicCutoff,ite_eq_right hx] using Real.smoothTransition.nonneg (-Real.log x/L),
      by simpa only [logarithmicCutoff,ite_eq_right hx] using Real.smoothTransition.le_one (-Real.log x/L)⟩

lemma logarithmicCutoff_support {L : ℝ} (hL : 0 < L) :
    tsupport (logarithmicCutoff L) ⊆ Icc (-1:ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hab : |x| < 1 := lt_of_not_ge (fun h => hx (logarithmicCutoff_zero hL h))
  exact ⟨(abs_lt.mp hab).1.le,(abs_lt.mp hab).2.le⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
