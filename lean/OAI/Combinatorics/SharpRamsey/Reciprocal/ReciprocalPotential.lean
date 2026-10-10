import Mathlib

namespace OAI

section
namespace SharpLogRamsey.ReciprocalPotential
open Real

lemma gap_nonneg {a s : ℝ} (hs : 0<s) (hsa : s≤a) : 0≤log (a/s) := by
  exact log_nonneg ((one_le_div hs).mpr hsa)

theorem gap_identity {a b s t Q : ℝ} (ha : 0<a) (hb : 0<b)
    (hs : 0<s) (ht : 0<t) (hQ : 0<Q) :
    log (a/s)+log (b/t)=log (a*b/Q)+log (Q/(s*t)) := by
  simp only [log_div (mul_ne_zero ha.ne' hb.ne') hQ.ne',
    log_div ha.ne' hs.ne',log_div hb.ne' ht.ne',
    log_div hQ.ne' (mul_ne_zero hs.ne' ht.ne'),
    log_mul ha.ne' hb.ne',log_mul hs.ne' ht.ne']
  ring

theorem gap_sum {a b s t Q K : ℝ} (ha : 0<a) (hb : 0<b)
    (hs : 0<s) (ht : 0<t) (hQ : 0<Q) (hprod : Q*exp (-K)≤ s*t) :
    log (a/s)+log (b/t)≤log (a*b/Q)+K := by
  rw [gap_identity ha hb hs ht hQ]
  apply add_le_add le_rfl
  apply (log_le_iff_le_exp (div_pos hQ (mul_pos hs ht))).mpr
  apply (div_le_iff₀ (mul_pos hs ht)).mpr
  have H := mul_le_mul_of_nonneg_right hprod (exp_nonneg K)
  have he : exp (-K)*exp K=1 := by rw [←exp_add]; simp
  nlinarith [show Q*exp (-K)*exp K=Q by rw [mul_assoc,he,mul_one]]

theorem cap_potential {b t Q C a' : ℝ} (hb : 0<b) (ht : 0<t)
    (hQ : 0<Q) (hC : 1≤C) (htb : t≤b) (ha' : 0<a')
    (hcap : a'≤C*Q/t) :
    max (log (a'*b/Q)) 0≤log (b/t)+log C := by
  have hc : 0<C := lt_of_lt_of_le zero_lt_one hC
  apply max_le
  · have hle : a'*b/Q≤C*(b/t) := by
      apply (div_le_iff₀ hQ).mpr
      have H := mul_le_mul_of_nonneg_right hcap hb.le
      have he : (C*Q/t)*b=C*(b/t)*Q := by ring
      exact H.trans_eq he
    have hp : 0<a'*b/Q := div_pos (mul_pos ha' hb) hQ
    have H := log_le_log hp hle
    rw [log_mul hc.ne' (div_pos hb ht).ne'] at H
    linarith
  · exact add_nonneg (gap_nonneg ht htb) (log_nonneg hC)

theorem branch {a b s t Q C K a' b' : ℝ} (ha : 0<a) (hb : 0<b)
    (hs : 0<s) (ht : 0<t) (hQ : 0<Q) (hC : 1≤C)
    (hsa : s≤a) (htb : t≤b) (ha' : 0<a') (hb' : 0<b')
    (hprodu : Q*exp (-K)≤ s*t) (hcapA : a'≤C*Q/t) (hcapB : b'≤C*Q/s) :
    max (log (a'*b/Q)) 0+max (log (a*b'/Q)) 0≤
      max (log (a*b/Q)) 0+K+2*log C := by
  have hl := cap_potential hb ht hQ hC htb ha' hcapA
  have hr := cap_potential ha hs hQ hC hsa hb' hcapB
  have hg := gap_sum ha hb hs ht hQ hprodu
  rw [mul_comm b' a] at hr
  have hm : log (a*b/Q)≤ max (log (a*b/Q)) 0 := le_max_left _ _
  linarith

end SharpLogRamsey.ReciprocalPotential

end

end OAI
