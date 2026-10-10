import Mathlib
import OAI.Combinatorics.SharpRamsey.Validation.ValidationCosts
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalPotential

namespace OAI

section
namespace SharpLogRamsey.Validation
open Real
noncomputable section

lemma index_scheduleLength_le {q u t : ℝ} (hq : 1≤q) (ht : 0<t) (htu : t≤u) :
    (scheduleLength q u t:ℝ)≤21*q*(log (u/t)+2) := by
  have hd : 0≤log (u/t) := log_nonneg ((le_div_iff₀ ht).mpr (by simpa using htu))
  have hx : 0≤20*q*(log (u/t)+2) := by positivity
  have hc := Nat.ceil_lt_add_one hx
  change (⌈20*q*(log (u/t)+2)⌉₊:ℝ)≤_
  have hqd : 2≤q*(log (u/t)+2) := by nlinarith
  nlinarith

lemma scheduleCutoff_log {q a : ℝ} (hq : 1≤q) (ha : 0≤a) (h : ℕ) :
    log ((scheduleCutoff q a h:ℝ)+1)≤(h:ℝ)*a+log (4*q) := by
  have he : 1≤exp ((h:ℝ)*a) := one_le_exp (by positivity)
  have hx : 0≤2*q*exp ((h:ℝ)*a) := by positivity
  have hc := Nat.ceil_lt_add_one hx
  have hq0 : 0<q := by linarith
  have hb : (scheduleCutoff q a h:ℝ)+1≤4*q*exp ((h:ℝ)*a) := by
    dsimp only [scheduleCutoff]
    have hp : 1≤q*exp ((h:ℝ)*a) := by nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr he)]
    nlinarith
  calc
    _ ≤ log (4*q*exp ((h:ℝ)*a)) := log_le_log (by positivity) hb
    _ = _ := by rw [log_mul (by positivity) (exp_ne_zero _),log_exp]; ring

theorem reciprocal_index_cost {q a u v s t : ℝ}
    (hq : 1≤q) (ha : 0≤a) (hs : 0<s) (ht : 0<t) (hsu : s≤u) (htv : t≤v) :
    log ((scheduleCutoff q a (scheduleLength q v t):ℝ)+1)+
      log ((scheduleCutoff q a (scheduleLength q u s):ℝ)+1)≤
      21*q*a*(log (u/s)+log (v/t)+4)+2*log (4*q) := by
  have h1 := scheduleCutoff_log hq ha (scheduleLength q v t)
  have h2 := scheduleCutoff_log hq ha (scheduleLength q u s)
  have h3 := mul_le_mul_of_nonneg_right (index_scheduleLength_le hq ht htv) ha
  have h4 := mul_le_mul_of_nonneg_right (index_scheduleLength_le hq hs hsu) ha
  linarith

theorem local_index_budget {q a u v s t Q b P J L : ℝ}
    (hq : 1 ≤ q) (ha : 0 ≤ a) (haP : a ≤ P) (hP : 4 ≤ P) (hJ : 0 ≤ J)
    (hs : 0<s) (ht : 0<t) (hsu : s ≤ u) (htv : t ≤ v) (hQ : 0<Q)
    (_hb : 0 ≤ b) (hbP : b ≤ P) (hprod : Q*exp (-b) ≤ s*t)
    (hlib : L ≤ J*q*P*(log (u/s)+log (v/t)+P)) :
    L+log ((scheduleCutoff q a (scheduleLength q v t):ℝ)+1)+
      log ((scheduleCutoff q a (scheduleLength q u s):ℝ)+1) ≤
      (2*(J+22)*q*P)*(max (log (u*v/Q)) 0+P) := by
  let d := log (u/s)+log (v/t)
  have hd : 0 ≤ d := add_nonneg (ReciprocalPotential.gap_nonneg hs hsu)
    (ReciprocalPotential.gap_nonneg ht htv)
  have hq0 : 0<q := by linarith
  have hP0 : 0<P := by linarith
  have hv := reciprocal_index_cost hq ha hs ht hsu htv
  have hval : 21*q*a*(d+4) ≤ 21*q*P*(d+P) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left haP (by positivity))
      (by linarith) (by linarith) (by positivity)
  have hlog : log (4*q) ≤ 4*q := (log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hbase : 8*q ≤ q*P*(d+P) := by
    have hmul := mul_le_mul_of_nonneg_left (show 8 ≤ P*(d+P) by nlinarith) hq0.le
    nlinarith only [hmul]
  have hloc : L+log ((scheduleCutoff q a (scheduleLength q v t):ℝ)+1)+
      log ((scheduleCutoff q a (scheduleLength q u s):ℝ)+1) ≤
      (J+22)*q*P*(d+P) := by
    dsimp only [d] at hval hbase
    nlinarith only [hlib,hv,hval,hlog,hbase]
  have hgap := ReciprocalPotential.gap_sum (hs.trans_le hsu) (ht.trans_le htv) hs ht hQ hprod
  have hm : log (u*v/Q) ≤ max (log (u*v/Q)) 0 := le_max_left _ _
  have hm0 : 0 ≤ max (log (u*v/Q)) 0 := le_max_right _ _
  have hd' : d+P ≤ 2*(max (log (u*v/Q)) 0+P) := by
    dsimp only [d]
    linarith
  apply hloc.trans
  have hcoef : 0 ≤ (J+22)*q*P := by positivity
  convert mul_le_mul_of_nonneg_left hd' hcoef using 1; ring

end
end SharpLogRamsey.Validation

end

end OAI
