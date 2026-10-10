import OAI.Geometry.Relativity.CKS.BendingProfiles
import OAI.Geometry.Relativity.CKS.RadialPrimitive

namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

def paddingWeight (R r : ℝ) : ℝ := Real.smoothTransition (r/R-1)
def paddingMass (R : ℝ) : ℝ → ℝ := primitive R (fun s => paddingWeight R s * paddingDensity s)
def heatDensity (R r : ℝ) : ℝ := bendingZeta R r / (2*r*(1+(bendingV R r)^2))
def heatTime (R : ℝ) : ℝ → ℝ := primitive (3*R) (heatDensity R)

lemma paddingWeight_smooth (R : ℝ) : ContDiff ℝ ∞ (paddingWeight R) := by
  unfold paddingWeight
  fun_prop
lemma paddingWeight_nonneg (R r : ℝ) : 0 ≤ paddingWeight R r := Real.smoothTransition.nonneg _
lemma paddingWeight_le_one (R r : ℝ) : paddingWeight R r ≤ 1 := Real.smoothTransition.le_one _
lemma paddingWeight_monotone {R : ℝ} (hR : 0 < R) : Monotone (paddingWeight R) := by
  intro x y hxy
  exact Real.smoothTransition.monotone (sub_le_sub_right ((div_le_div_iff_of_pos_right hR).mpr hxy) _)
lemma paddingWeight_zero {R r : ℝ} (hR : 0 < R) (hr : r ≤ R) : paddingWeight R r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hh : r/R ≤ 1 := (div_le_iff₀ hR).mpr (by simpa using hr)
  linarith
lemma paddingWeight_one {R r : ℝ} (hR : 0 < R) (hr : 2*R ≤ r) : paddingWeight R r = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hh : 2 ≤ r/R := (le_div_iff₀ hR).mpr hr
  linarith
lemma paddingIntegrand_smooth (R : ℝ) :
    ContDiffOn ℝ ∞ (fun r => paddingWeight R r * paddingDensity r) (Ioi 0) :=
  (paddingWeight_smooth R).contDiffOn.mul paddingDensity_smooth
lemma paddingMass_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (paddingMass R) (Ioi 0) :=
  primitive_smooth (paddingIntegrand_smooth R) hR
lemma paddingMass_hasDerivAt {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    HasDerivAt (paddingMass R) (paddingWeight R r * paddingDensity r) r :=
  primitive_hasDerivAt (paddingIntegrand_smooth R).continuousOn hR hr
lemma paddingMass_initial {R r : ℝ} (hR : 0 < R) (hr : r ≤ R) : paddingMass R r = 0 := by
  apply intervalIntegral.integral_zero_ae
  filter_upwards [] with s hs
  rw [uIoc_of_ge hr] at hs
  simp only [paddingWeight_zero hR hs.2,zero_mul]
lemma paddingMass_nonneg {R r : ℝ} (hR : 0 < R) (_hr : 0 < r) : 0 ≤ paddingMass R r := by
  by_cases h : r ≤ R
  · rw [paddingMass_initial hR h]
  · apply intervalIntegral.integral_nonneg (le_of_not_ge h)
    intro s hs
    exact mul_nonneg (paddingWeight_nonneg _ _) (paddingDensity_nonneg (hR.trans_le hs.1))

lemma paddingMass_weighted_bound {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    paddingMass R r ≤ paddingWeight R r * (2/Real.sqrt R) := by
  have hrp : 0 < r := hR.trans_le hr
  have hint := positive_interval_integrable (paddingIntegrand_smooth R).continuousOn hR hrp
  have hdint := positive_interval_integrable paddingDensity_smooth.continuousOn hR hrp
  have hh := intervalIntegral.integral_mono_on hr hint (hdint.const_mul (paddingWeight R r))
    (fun s hs => mul_le_mul_of_nonneg_right (paddingWeight_monotone hR hs.2)
      (paddingDensity_nonneg (hR.trans_le hs.1)))
  change paddingMass R r ≤ _ at hh
  rw [intervalIntegral.integral_const_mul] at hh
  change paddingMass R r ≤ paddingWeight R r * primitive R paddingDensity r at hh
  rw [paddingDensity_integral hR hrp] at hh
  have hw := paddingWeight_nonneg R r
  have hd : 0 ≤ 2/Real.sqrt r := by positivity
  nlinarith
lemma paddingMass_bound {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    paddingMass R r ≤ 2/Real.sqrt R := by
  exact (paddingMass_weighted_bound hR hr).trans
    (by have hh := paddingWeight_le_one R r
        have hp : 0 ≤ 2/Real.sqrt R := by positivity
        nlinarith)

lemma heatDensity_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (heatDensity R) (Ioi 0) := by
  unfold heatDensity
  exact (bendingZeta_smooth R).contDiffOn.div
    ((contDiffOn_const.mul contDiffOn_id).mul (contDiffOn_const.add ((bendingV_smooth hR).pow 2)))
    (fun r hr => ne_of_gt (mul_pos (mul_pos (by norm_num) hr) (by positivity)))
lemma heatDensity_nonneg {R r : ℝ} (hr : 0 < r) : 0 ≤ heatDensity R r := by
  exact div_nonneg (zeta_nonneg _) (by positivity)
lemma heatTime_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (heatTime R) (Ioi 0) :=
  primitive_smooth (heatDensity_smooth hR) (by positivity)
lemma heatTime_hasDerivAt {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    HasDerivAt (heatTime R) (heatDensity R r) r :=
  primitive_hasDerivAt (heatDensity_smooth hR).continuousOn (by positivity) hr
lemma heatTime_initial {R r : ℝ} (hR : 0 < R) (hr : r ≤ 4*R) : heatTime R r = 0 := by
  apply intervalIntegral.integral_zero_ae
  filter_upwards [] with s hs
  have hsr : s ≤ 4*R := hs.2.trans (max_le (by linarith) hr)
  have hh : s/R ≤ 4 := (div_le_iff₀ hR).mpr hsr
  simp [heatDensity,bendingZeta,zeta_zero hh]
lemma heatTime_nonneg {R r : ℝ} (hR : 0 < R) (_hr : 0 < r) : 0 ≤ heatTime R r := by
  by_cases h : r ≤ 4*R
  · rw [heatTime_initial hR h]
  · have h3 : 3*R ≤ r := by linarith
    apply intervalIntegral.integral_nonneg h3
    intro s hs
    exact heatDensity_nonneg (by linarith [hs.1])

end
end CKSBending

end

end OAI
