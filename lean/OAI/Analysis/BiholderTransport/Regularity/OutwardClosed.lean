import Mathlib

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section OutwardClosed
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma outward_closed_conditions {p r e:E} {d w a D ν:ℝ}
    (he:‖e‖=1) (hp:0 < inner ℝ p e) (hd:0 < d) (hr:r=p+d • e)
    (ha:0 < a) (hD:0 < D) (hq:a*D ≤ (inner ℝ p e)^2)
    (hm:ν*D/(inner ℝ p e) ≤ w*d) (hdb:d ≤ 3*D/(2*(inner ℝ p e))) :
    ν*D ≤ w*inner ℝ p (r-p) ∧
    a*D*‖r-p‖^2 ≤ (inner ℝ p (r-p))^2 ∧
    inner ℝ p (r-p) ≤ 3*D/2 ∧
    ‖r-p‖^2 ≤ (9/(4*a))*D := by
  have hrp:r-p=d • e:=by rw [hr]; abel
  have hi:inner ℝ p (r-p)=d*inner ℝ p e:=by rw [hrp,real_inner_smul_right]
  have hn:‖r-p‖=d:=by rw [hrp,norm_smul,Real.norm_eq_abs,abs_of_pos hd,he,mul_one]
  have Hm:ν*D ≤ w*d*(inner ℝ p e):=(div_le_iff₀ hp).mp hm
  have Hdb:d*(2*inner ℝ p e) ≤ 3*D:=(le_div_iff₀ (mul_pos (by norm_num) hp)).mp hdb
  have Hsq:(d*inner ℝ p e)^2 ≤ (3*D/2)^2:=by
    apply (sq_le_sq₀ (mul_nonneg hd.le hp.le) (by positivity)).mpr
    linarith only [Hdb]
  have Hq:=mul_le_mul_of_nonneg_right hq (sq_nonneg d)
  have Hlast:d^2 ≤ (9/(4*a))*D:=by
    apply (mul_le_mul_iff_right₀ (mul_pos ha hD)).mp
    have hh:(a*D)*((9/(4*a))*D)=(3*D/2)^2:=by field_simp; ring
    rw [hh]
    calc a*D*d^2 ≤ (inner ℝ p e)^2*d^2:=Hq
         _ = (d*inner ℝ p e)^2:=by ring
         _ ≤ _:=Hsq
  refine ⟨?_,?_,?_,?_⟩
  · rw [hi]; nlinarith only [Hm]
  · rw [hn,hi]; nlinarith only [Hq]
  · rw [hi]; linarith only [Hdb]
  · rwa [hn]

lemma outward_direction_of_closed_conditions {p r:E} {w a D ν:ℝ}
    (hw:0 < w) (_:0 < a) (hD:0 < D) (hν:0 < ν)
    (hm:ν*D ≤ w*inner ℝ p (r-p))
    (hq:a*D*‖r-p‖^2 ≤ (inner ℝ p (r-p))^2)
    (hi:inner ℝ p (r-p) ≤ 3*D/2)
    (hn:‖r-p‖^2 ≤ (9/(4*a))*D) :
    ∃e:E,∃d:ℝ,‖e‖=1 ∧ 0 < d ∧ r=p+d • e ∧
      0 < inner ℝ p e ∧ a*D ≤ (inner ℝ p e)^2 ∧
      ν*D/(inner ℝ p e) ≤ w*d ∧
      d ≤ 3*D/(2*(inner ℝ p e)) ∧
      ‖r‖^2-‖p‖^2 ≤ (3+9/(4*a))*D := by
  have hp:0 < inner ℝ p (r-p):=by
    have H:0 < w*inner ℝ p (r-p):=(mul_pos hν hD).trans_le hm
    exact (mul_pos_iff_of_pos_left hw).mp H
  have hv:r-p≠0:=by intro H; rw [H,inner_zero_right] at hp; exact lt_irrefl _ hp
  have hd:0 < ‖r-p‖:=norm_pos_iff.mpr hv
  let e:E:=‖r-p‖⁻¹ • (r-p)
  have he:‖e‖=1:=by simp only [e,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hd,inv_mul_cancel₀ hd.ne']
  have hr:r=p+‖r-p‖ • e:=by
    simp only [e,smul_smul,mul_inv_cancel₀ hd.ne',one_smul]
    abel
  have hpe:inner ℝ p e=inner ℝ p (r-p)/‖r-p‖:=by
    simp only [e,real_inner_smul_right,div_eq_mul_inv,mul_comm]
  have hpep:0 < inner ℝ p e:=by rw [hpe]; exact div_pos hp hd
  refine ⟨e,‖r-p‖,he,hd,hr,hpep,?_,?_,?_,?_⟩
  · rw [hpe,div_pow]
    exact (le_div_iff₀ (sq_pos_of_pos hd)).mpr hq
  · apply (div_le_iff₀ hpep).mpr
    rw [hpe]
    have HH:w*‖r-p‖*(inner ℝ p (r-p)/‖r-p‖)=w*inner ℝ p (r-p):=by
      field_simp
    rwa [HH]
  · apply (le_div_iff₀ (mul_pos (by norm_num) hpep)).mpr
    rw [hpe]
    have H:‖r-p‖*(2*(inner ℝ p (r-p)/‖r-p‖))=2*inner ℝ p (r-p):=by field_simp
    rw [H]
    linarith only [hi]
  · have H:‖r‖^2=‖p‖^2+2*inner ℝ p (r-p)+‖r-p‖^2:=by
      conv_lhs => rw [show r=p+(r-p) by abel]
      exact norm_add_sq_real _ _
    nlinarith only [H,hi,hn]

end OutwardClosed
end WeakMTWTransport

end
end

end OAI
