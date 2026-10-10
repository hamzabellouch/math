import OAI.MathematicalPhysics.Transonic.Core

namespace OAI

section
noncomputable section

namespace SepticProfile.ShootingParameters
open Set
lemma q_bounds {t : ℝ} (ht : t ∈ Icc leftEnd rightEnd) :
    3499/1500<q t ∧ q t<7/3 := by
  have hb := beta_bounds ht
  rw [(parameter_identities ht).1]
  constructor <;> linarith [hb.1,hb.2]

lemma kappa_bounds {t : ℝ} (ht : t ∈ Icc leftEnd rightEnd) :
    -(1/500:ℝ)<kappa t ∧ kappa t<0 := by
  have hb := beta_bounds ht
  have hq := q_bounds ht
  have hq0 : 0<q t := by linarith [hq.1]
  rw [(parameter_identities ht).2.2]
  constructor
  · rw [lt_div_iff₀ hq0]
    nlinarith [hq.1,hb.2]
  · exact div_neg_of_neg_of_pos (by linarith [hb.1]) hq0

lemma sigma_shooting_bounds {t : ℝ} (ht : t ∈ Icc leftEnd rightEnd) :
    (991/1000:ℝ)<sigma t ∧ sigma t<993/1000 := by
  have hq := q_bounds ht
  have hq0 : 0<q t := by linarith [hq.1]
  have hql : (3499/1500:ℝ)^2<(q t)^2 := by
    nlinarith [mul_pos (by linarith [hq.1] : 0<q t-3499/1500)
      (by linarith : 0<q t+3499/1500)]
  have hqu : (q t)^2<(7/3:ℝ)^2 := by
    nlinarith [mul_pos (sub_pos.mpr hq.2) (by linarith : 0<7/3+q t)]
  rw [(parameter_identities ht).2.1]
  have hd : 0<5*(q t)^2 := by positivity
  constructor
  · rw [lt_div_iff₀ hd]
    nlinarith
  · rw [div_lt_iff₀ hd]
    nlinarith
end SepticProfile.ShootingParameters

end
end

end OAI
