import OAI.Analysis.BernoulliCone.OuterGeometry

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
lemma GSup_neg_deriv {t:ℝ} (hl:t7≤t) (hr:t≤27/50) : deriv GSup t<0 := by
  have ht0:0≤t:=t7_pos.le.trans hl
  have ht1:t<1:=by linarith
  have hI:t∈Ioo (-1:ℝ) 1:=⟨by linarith,ht1⟩
  have hf0:f t≤0 := by
    have hh:=f_strictAnti.antitoneOn ⟨t7_pos.le,t7_lt_one⟩ ⟨ht0,ht1⟩ hl
    simpa only [f_t7] using hh
  have hf:-1/8≤f t := upper_endpoint_bounds.1.trans
    (f_strictAnti.antitoneOn ⟨ht0,ht1⟩ (by norm_num) hr)
  have hp:fp t≤-4 := (fp_strictAnti.antitoneOn (by norm_num) ⟨ht0,ht1⟩
    (by linarith [t7_bounds.1])).trans upper_endpoint_bounds.2
  obtain ⟨hq0,hq4,hqL⟩:=qSup_small ht0 hr
  have hm:=mul_le_mul_of_nonneg_left hq4 (show 0≤-f t by linarith)
  have hB:fp t-4*f t*qSup t≤0 := by nlinarith
  have hc : 5*t-(1-t^2)*qSup t<0 := by
    have hu : t^2≤729/2500 := by nlinarith
    have hd : 1-t^2≠0 := by nlinarith
    have he : (1-t^2)*qSup t-5*t=t*(1-3*t^2)/(1+t^2) := by
      unfold qSup
      field_simp [hd,show 1+t^2≠0 by positivity]
      ring
    have hpos : 0<t*(1-3*t^2)/(1+t^2) :=
      div_pos (mul_pos (t7_pos.trans_le hl) (by linarith)) (by positivity)
    linarith
  have hbb : fp t-f t*qSup t<0 := by nlinarith
  rw [(hasDerivAt_GSup hI).deriv]
  have hh1 := mul_neg_of_neg_of_pos hc (sq_pos_of_ne_zero (ne_of_lt hbb))
  have hh2 := mul_nonneg_of_nonpos_of_nonpos hf0 hB
  nlinarith

lemma GSup_near_lt {t:ℝ} (hl:t7<t) (hr:t≤27/50) : GSup t<c7 := by
  have hanti:StrictAntiOn GSup (Icc t7 (27/50)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · intro x hx
      exact (hasDerivAt_GSup ⟨by linarith [hx.1,t7_pos],by linarith [hx.2]⟩).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact GSup_neg_deriv hx.1.le hx.2.le
  have he:GSup t7=c7 := by simp [GSup,f_t7,c7]
  rw [←he]
  exact hanti ⟨le_rfl,by linarith [t7_bounds.2]⟩ ⟨hl.le,hr⟩ hl

lemma c7_lower_strict : 17734/1000<c7 := by
  have hl:t7^2≤(517331/1000000:ℝ)^2 := by nlinarith [t7_bounds.2,t7_pos]
  have hu:1-t7^2≤1-(517330/1000000:ℝ)^2 := by nlinarith [t7_bounds.1,t7_pos]
  have hd:0<1-t7^2 := by nlinarith [t7_pos,t7_lt_one]
  have hp:=pow_le_pow_left₀ hd.le hu 5
  have hm:=mul_le_mul hl hp (by positivity : (0:ℝ)≤(1-t7^2)^5) (by norm_num)
  rw [c7_eq]
  apply (lt_div_iff₀ (mul_pos (sq_pos_of_pos t7_pos) (pow_pos hd 5))).mpr
  nlinarith

lemma GSup_far_lt {t:ℝ} (hl:27/50≤t) (hr:t≤3/5) : GSup t<c7 := by
  have ht:0<t:=by linarith
  have ht1:t<1:=by linarith
  have hd:0<1-t^2:=by nlinarith
  have hul:729/2500≤t^2:=by nlinarith
  have hur:t^2≤9/25:=by nlinarith
  obtain ⟨hL,hH⟩:=numerator_scaled_bounds ht.le ht1
  have hplo:=UpperAlgebra.bound_lo hul hur
  have hphi:=UpperAlgebra.bound_hi hul hur
  have identity (F:ℝ) : UpperAlgebra.numerator (t^2) F =
      (9*t^2*(1-t^2)*(1+t^2)^2+(1-6*t^2-3*(t^2)^2)^2)*F^2+
        (-16*(1-6*t^2-3*(t^2)^2)*(1+t^2))*F+64*(1+t^2)^2 := by
    unfold UpperAlgebra.numerator
    ring
  simp only [identity] at hplo hphi
  have hA:0≤9*t^2*(1-t^2)*(1+t^2)^2+(1-6*t^2-3*(t^2)^2)^2:=by positivity
  have hh:=quadratic_bound hA hL hH hplo hphi
  rw [←identity,←GSup_numerator ht ht1] at hh
  have hden:0<UpperAlgebra.denominator (t^2):=by unfold UpperAlgebra.denominator; positivity
  exact ((mul_le_mul_iff_left₀ hden).mp hh).trans_lt c7_lower_strict

theorem GSup_lt_c7 {t:ℝ} (hl:t7<t) (hr:t≤3/5) : GSup t<c7 := by
  by_cases h:t≤27/50
  · exact GSup_near_lt hl h
  · exact GSup_far_lt (le_of_lt (lt_of_not_ge h)) hr
end Bernoulli.DeSilvaJerison

end
end

end OAI
