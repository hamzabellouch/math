import OAI.Probability.RadialTransition.SupportControl

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def rawBumpProfile (r : ℝ) : ℝ := Real.smoothTransition (2 - 2 * r ^ 2)

def rawBump (x : Position) : ℝ := rawBumpProfile ‖x‖

theorem rawBumpProfile_nonneg (r : ℝ) : 0 ≤ rawBumpProfile r :=
  Real.smoothTransition.nonneg _

theorem rawBumpProfile_le_one (r : ℝ) : rawBumpProfile r ≤ 1 :=
  Real.smoothTransition.le_one _

theorem rawBumpProfile_zero {r : ℝ} (hr : 1 ≤ r) : rawBumpProfile r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith

theorem continuous_rawBumpProfile : Continuous rawBumpProfile := by
  exact Real.smoothTransition.continuous.comp (by fun_prop)

theorem contDiff_rawBump : ContDiff ℝ ∞ rawBump := by
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))

theorem compactSupport_rawBump : HasCompactSupport rawBump := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Position) 1)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hx (rawBumpProfile_zero (le_of_not_ge h))

def bumpIntegral : ℝ := ∫ x : Position, rawBump x

theorem bumpIntegral_pos : 0 < bumpIntegral := by
  apply contDiff_rawBump.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    compactSupport_rawBump (fun x => rawBumpProfile_nonneg ‖x‖) (x := 0)
  simp [rawBump, rawBumpProfile, Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2)]

def bumpProfile (r : ℝ) : ℝ := rawBumpProfile r / bumpIntegral

def bump (x : Position) : ℝ := bumpProfile ‖x‖

theorem bumpProfile_nonneg (r : ℝ) : 0 ≤ bumpProfile r :=
  div_nonneg (rawBumpProfile_nonneg r) bumpIntegral_pos.le

theorem bumpProfile_bound (r : ℝ) : |bumpProfile r| ≤ bumpIntegral⁻¹ := by
  rw [abs_of_nonneg (bumpProfile_nonneg r)]
  simpa [bumpProfile, one_div] using
    div_le_div_of_nonneg_right (rawBumpProfile_le_one r) bumpIntegral_pos.le

theorem bumpProfile_zero {r : ℝ} (hr : 1 ≤ r) : bumpProfile r = 0 := by
  rw [bumpProfile, rawBumpProfile_zero hr, zero_div]

theorem continuous_bumpProfile : Continuous bumpProfile :=
  continuous_rawBumpProfile.div_const _

theorem contDiff_bump : ContDiff ℝ ∞ bump := contDiff_rawBump.div_const _

theorem compactSupport_bump : HasCompactSupport bump := by
  apply compactSupport_rawBump.mono
  intro x hx hr
  apply hx
  change rawBump x / bumpIntegral = 0
  rw [hr, zero_div]

theorem integral_bump : ∫ x : Position, bump x = 1 := by
  change (∫ x : Position, rawBump x / bumpIntegral) = 1
  rw [integral_div, ← bumpIntegral, div_self bumpIntegral_pos.ne']

end RadialTransition

end

end OAI
