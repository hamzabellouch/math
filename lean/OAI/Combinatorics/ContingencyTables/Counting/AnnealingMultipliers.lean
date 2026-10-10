import Mathlib

namespace OAI

/-!
# The companion's multiplier update from empirical type counts

The old multiplier cancels from the update relative to the current ideal
multiplier. Relative accuracy of two positive type means, followed by the
proved adjacent-parameter factor two, gives the required factor four at
the next parameter. This is deterministic algebra of the actual update.
-/

namespace ContingencyTables.AnnealingMultipliers

variable {eta p q ph qh w ideal nextIdeal : ℝ}

theorem empirical_positive (hp : 0<p) (he : eta≤1/4)
    (hph : (1-eta)*p≤ph) : 0<ph := by
  have h : 0<(1-eta)*p := mul_pos (by linarith) hp
  exact h.trans_le hph

/-- The normalized ratio of two empirically observed positive means. -/
theorem relative_ratio (hp : 0<p) (hq : 0<q) (he0 : 0≤eta) (he : eta≤1/4)
    (hph : (1-eta)*p≤ph ∧ ph≤(1+eta)*p)
    (hqh : (1-eta)*q≤qh ∧ qh≤(1+eta)*q) :
    0<ph*q/(qh*p) ∧
      1/2≤ph*q/(qh*p) ∧ ph*q/(qh*p)≤2 ∧
      |Real.log (ph*q/(qh*p))|≤4*eta := by
  have hp' := empirical_positive hp he hph.1
  have hq' := empirical_positive hq he hqh.1
  have hden : 0<qh*p := mul_pos hq' hp
  have hr : 0<ph*q/(qh*p) := div_pos (mul_pos hp' hq) hden
  have hlow : (1-eta)*(p*q)≤ph*q := by nlinarith [mul_le_mul_of_nonneg_right hph.1 hq.le]
  have hupp : ph*q≤(1+eta)*(p*q) := by nlinarith [mul_le_mul_of_nonneg_right hph.2 hq.le]
  have dlow : (1-eta)*(p*q)≤qh*p := by nlinarith [mul_le_mul_of_nonneg_right hqh.1 hp.le]
  have dupp : qh*p≤(1+eta)*(p*q) := by nlinarith [mul_le_mul_of_nonneg_right hqh.2 hp.le]
  have hpq : 0≤p*q := (mul_pos hp hq).le
  have htwice : (1+eta)*(p*q)≤2*((1-eta)*(p*q)) := by
    have := mul_nonneg (show 1-3*eta≥0 by linarith) hpq
    nlinarith
  have hlo : 1/2≤ph*q/(qh*p) := by
    rw [le_div_iff₀ hden]
    linarith
  have hup : ph*q/(qh*p)≤2 := by
    rw [div_le_iff₀ hden]
    linarith
  have hstretch : (1+eta)*(p*q)≤(1+4*eta)*((1-eta)*(p*q)) := by
    have hcoeff : 0≤2*eta-4*eta^2 := by nlinarith
    have := mul_nonneg hcoeff hpq
    nlinarith
  have hscale : 0≤1+4*eta := by linarith
  have hrup : ph*q/(qh*p)≤1+4*eta := by
    rw [div_le_iff₀ hden]
    have := mul_le_mul_of_nonneg_left dlow hscale
    nlinarith
  have hinvup : (ph*q/(qh*p))⁻¹≤1+4*eta := by
    rw [inv_div]
    rw [div_le_iff₀ (mul_pos hp' hq)]
    have := mul_le_mul_of_nonneg_left hlow hscale
    nlinarith
  have hlogup := Real.log_le_sub_one_of_pos hr
  have hloglo := Real.one_sub_inv_le_log_of_pos hr
  refine ⟨hr,hlo,hup,abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith

/-- The concrete update w*(observed plain count)/(observed defect count)
is good for the next parameter. Earlier multiplier errors do not compound. -/
theorem update_good (hp : 0<p) (hq : 0<q) (hw : 0<w)
    (he0 : 0≤eta) (he : eta≤1/4)
    (hph : (1-eta)*p≤ph ∧ ph≤(1+eta)*p)
    (hqh : (1-eta)*q≤qh ∧ qh≤(1+eta)*q)
    (hideal : w*p/q=ideal)
    (hnext : ideal/2≤nextIdeal ∧ nextIdeal≤2*ideal) :
    nextIdeal/4≤w*ph/qh ∧ w*ph/qh≤4*nextIdeal := by
  have h := relative_ratio hp hq he0 he hph hqh
  have hq' := empirical_positive hq he hqh.1
  have hi : 0 < ideal := by rw [← hideal]; positivity
  have hid : w*ph/qh=ideal*(ph*q/(qh*p)) := by
    rw [← hideal]
    field_simp [ne_of_gt hp,ne_of_gt hq,ne_of_gt hq']
  rw [hid]
  have hlo := mul_le_mul_of_nonneg_left h.2.1 hi.le
  have hup := mul_le_mul_of_nonneg_left h.2.2.1 hi.le
  constructor <;> nlinarith [hnext.1,hnext.2]

end ContingencyTables.AnnealingMultipliers

end OAI
