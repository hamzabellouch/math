import Mathlib

namespace OAI

                                    
section

/-! Companion §03, coarse epoch parameter gaps.  These explicit constants prove
 the manuscript's uniform logarithmic comparison without a compactness/minimum
 oracle.  Hypotheses are the exact held-size and non-dominance inequalities. -/
namespace UniformKServer.ParameterGaps
noncomputable section

/-- The regular size-log comparison, with an absolute explicit constant. -/
theorem regular_log {x : ℝ} (hx : (50:ℝ)/43 ≤ x) :
    (1+Real.log x)/50 ≤ Real.log (1+(9:ℝ)/11*((99:ℝ)/100*x-1)) := by
  have hx₀ : 0 < x := by linarith
  let q := 1+(9:ℝ)/11*((99:ℝ)/100*x-1)
  have hq : (x+(21:ℝ)/20)/2 ≤ q := by dsimp [q]; linarith
  have hq₀ : 0 < q := by linarith
  have hs : (21:ℝ)/20*x ≤ q^2 := by nlinarith [sq_nonneg (x-(21:ℝ)/20)]
  have hl := Real.log_le_log (show 0 < (21:ℝ)/20*x by positivity) hs
  rw [Real.log_mul (by norm_num : (21:ℝ)/20 ≠ 0) hx₀.ne', Real.log_pow] at hl
  have hc : (1:ℝ)/21 ≤ Real.log ((21:ℝ)/20) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : 0 < (21:ℝ)/20)
    norm_num at h ⊢
    exact h
  have hxlog := Real.log_nonneg (show 1 ≤ x by linarith)
  change (1+Real.log x)/50 ≤ Real.log q
  norm_num at hl
  linarith

/-- Convert exact active accuracy and superadditivity to the size ratio.
    The side sum may omit inactive children, whose sizes remain nonnegative. -/
theorem ratio_from_sizes {M m a side : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hacc : (9:ℝ)/10*m ≤ a) (hside : 0 ≤ side)
    (hM : m+(10:ℝ)/11*side ≤ M) :
    1+(9:ℝ)/11*(side/a) ≤ M/m := by
  apply (le_div_iff₀ hm).mpr
  have hratio : (9:ℝ)/11*(side/a)*m ≤ (10:ℝ)/11*side := by
    apply (mul_le_mul_iff_left₀ ha).mp
    have hcancel : ((9:ℝ)/11*(side/a)*m)*a = (9:ℝ)/11*side*m := by
      field_simp
    rw [hcancel]
    nlinarith
  nlinarith

/-- A regular active child in an epoch. -/
theorem regular_epoch {A a M m : ℝ} (ha : 0 < a)
    (hsmall : a ≤ (86:ℝ)/100*A)
    (hratio : 1+(9:ℝ)/11*((99:ℝ)/100*A/a-1) ≤ M/m) :
    (1+Real.log (A/a))/50 ≤ Real.log (M/m) := by
  have hx : (50:ℝ)/43 ≤ A/a := by
    apply (le_div_iff₀ ha).mpr
    linarith
  have hq : 0 < 1+(9:ℝ)/11*((99:ℝ)/100*(A/a)-1) := by linarith
  refine (regular_log hx).trans (Real.log_le_log hq ?_)
  simpa only [mul_div_assoc] using hratio

/-- The same comparison for the marked child.  The constant 1/2 is a
    conservative consequence of the source's side/reference comparisons. -/
theorem dominant_log {u r : ℝ} (hu : 0 ≤ u) (hu₁ : u ≤ 1/4)
    (hr : 1+u/2 ≤ r) : u/3 ≤ Real.log r := by
  have hp : 0 < 1+u/2 := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hm := Real.log_le_log hp hr
  have he : 1-(1+u/2)⁻¹ = (u/2)/(1+u/2) := by field_simp; ring
  rw [he] at hl
  have hb : u/3 ≤ (u/2)/(1+u/2) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  linarith

/-- With δ_s=10⁻³, the marked side-reference gives the concrete ratio used
    in `dominant_log`.  No additive lower bound on u is needed. -/
theorem dominant_ratio {A a side U r : ℝ} (hA : 0 < A) (ha : 0 < a)
    (hside : 0 ≤ side) (haA : a ≤ (101:ℝ)/100*A)
    (hU : U ≤ (1001:ℝ)/1000*side)
    (hr : 1+(9:ℝ)/11*(side/a) ≤ r) :
    1+(U/A)/2 ≤ r := by
  have hb : (U/A)/2 ≤ (9:ℝ)/11*(side/a) := by
    apply (div_le_iff₀ (show (0:ℝ)<2 by norm_num)).mpr
    apply (div_le_iff₀ hA).mpr
    apply (mul_le_mul_iff_left₀ ha).mp
    have hc : ((9:ℝ)/11*(side/a)*2*A)*a = (18:ℝ)/11*side*A := by
      field_simp
      ring
    rw [hc]
    nlinarith [mul_le_mul_of_nonneg_right hU ha.le,
      mul_le_mul_of_nonneg_left haA hside]
  linarith

/-- Clipped β parameters are unclipped on active vertices. -/
def beta (c ell k cut M : ℝ) : ℝ := 3 + c / ell * Real.log (k/max M cut)

theorem beta_gap {c ell k cut M m : ℝ}
    (hk : 0 < k) (hm : 0 < m) (hM : 0 < M)
    (hcm : cut ≤ m) (hcM : cut ≤ M) :
    beta c ell k cut m-beta c ell k cut M = c/ell * Real.log (M/m) := by
  simp only [beta,max_eq_left hcm,max_eq_left hcM,Real.log_div hk.ne' hm.ne',
    Real.log_div hk.ne' hM.ne',Real.log_div hM.ne' hm.ne']
  ring

end
end UniformKServer.ParameterGaps

end

end OAI
