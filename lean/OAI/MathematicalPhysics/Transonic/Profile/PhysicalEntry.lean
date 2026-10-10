import OAI.MathematicalPhysics.Transonic.Profile.PhysicalBounds

namespace OAI

section
noncomputable section
namespace SepticProfile.PhysicalExterior
open Set

lemma chart_antitone {y U V : ℝ} (hy : |y|<1)
    (hU : 0<1-y*U) (hV : 0<1-y*V) (hUV : U≤V) :
    velocityToU y V≤velocityToU y U := by
  rw [velocityToU,velocityToU,div_le_div_iff₀ hV hU]
  have hs : 0≤1-y^2 := by have := abs_lt.mp hy;nlinarith
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hUV)]

lemma chart_first {q y U : ℝ} (hd : 1-y*U≠0) :
    1-q*y+(q-y)*velocityToU y U=(1-y^2)*(1-q*U)/(1-y*U) := by
  unfold velocityToU
  field_simp
  ring
lemma chart_second {q y U : ℝ} (hd : 1-y*U≠0) :
    1+q*y-(y+q)*velocityToU y U=(1-y^2)*(1+q*U)/(1-y*U) := by
  unfold velocityToU
  field_simp
  ring
lemma chart_critical {ell beta y U : ℝ} (hd : 1-y*U≠0) :
    beta*ell*(1-(velocityToU y U)^2)*y-
      3*(velocityToU y U)*(1-y*velocityToU y U)=
    (1-y^2)/(1-y*U)^2*(beta*ell*y*(1-U^2)-3*(y-U)) := by
  unfold velocityToU
  field_simp
  ring

lemma normalized_critical {beta r z p : ℝ} (hr : r*SepticProfile.q beta=3*sonicSpeed) :
    beta*ell*(r*z)*(1-(sonicSpeed*p)^2)-3*(r*z-sonicSpeed*p)=
      3*sonicSpeed*(p-z)+(beta*r)*z*(1-p^2) := by
  have hc : ell*sonicSpeed^2=1 := by rw [sonicSpeed_sq];norm_num [ell]
  have hq : SepticProfile.q beta=3-beta*(ell-1) := rfl
  rw [hq] at hr
  linear_combination -(z)*hr - beta*r*z*p^2*hc

lemma critical_exit {beta r z p : ℝ} (hbeta : 1<beta)
    (hbeta1 : beta*(ell+Real.sqrt ell)<3)
    (hr : r=sonicRadius beta)
    (hy : |r*z|<1) (hU : |sonicSpeed*p|<1)
    (hexit : 0<p-z+(3/7*(1-SepticProfile.kappa beta))*z*(1-p^2)) :
    0<beta*ell*(1-(velocityToU (r*z) (sonicSpeed*p))^2)*(r*z)-
      3*(velocityToU (r*z) (sonicSpeed*p))*(1-(r*z)*velocityToU (r*z) (sonicSpeed*p)) := by
  have hp := source_parameter_bounds hbeta hbeta1
  have hc : 0<sonicSpeed := hp.2.1
  have hq : 0<SepticProfile.q beta := hp.2.2.2.1
  have hrr : r*SepticProfile.q beta=3*sonicSpeed := by
    rw [hr,sonicRadius_eq,div_mul_cancel₀ _ (ne_of_gt hq)]
  have hd : 0<1-(r*z)*(sonicSpeed*p) := by
    have hh : |(r*z)*(sonicSpeed*p)|<1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hy.le (abs_nonneg _)).trans_lt (by simpa using hU)
    linarith [(abs_lt.mp hh).2]
  rw [chart_critical (ne_of_gt hd),normalized_critical hrr]
  have hb : beta*r=(3*sonicSpeed)*(3/7*(1-SepticProfile.kappa beta)) := by
    rw [hr,sonicRadius_eq,SepticProfile.kappa]
    field_simp [ne_of_gt hq]
    unfold SepticProfile.q ell
    ring
  rw [hb]
  have hs : 0<1-(r*z)^2 := by have := abs_lt.mp hy;nlinarith
  apply mul_pos (div_pos hs (sq_pos_of_pos hd))
  have hh := mul_pos (mul_pos (by norm_num : (0:ℝ)<3) hc) hexit
  nlinarith

lemma sonic_exit_factors {r z p : ℝ} (hy : |r*z|<1)
    (hU : |sonicSpeed*p|<1) (hp : 1<p) :
    (1-Real.sqrt ell*(r*z)+(Real.sqrt ell-r*z)*velocityToU (r*z) (sonicSpeed*p)<0) ∧
    (0<1+Real.sqrt ell*(r*z)-(r*z+Real.sqrt ell)*velocityToU (r*z) (sonicSpeed*p)) := by
  have hc : Real.sqrt ell*sonicSpeed=1 := by
    unfold sonicSpeed
    exact mul_one_div_cancel (ne_of_gt (Real.sqrt_pos.mpr (by norm_num [ell])))
  have hd : 0<1-(r*z)*(sonicSpeed*p) := by
    have hh : |(r*z)*(sonicSpeed*p)|<1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hy.le (abs_nonneg _)).trans_lt (by simpa using hU)
    linarith [(abs_lt.mp hh).2]
  rw [chart_first (ne_of_gt hd),chart_second (ne_of_gt hd),←mul_assoc,hc,one_mul]
  have hs : 0<1-(r*z)^2 := by have := abs_lt.mp hy;nlinarith
  exact ⟨div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hs (by linarith)) hd,
    div_pos (mul_pos hs (by linarith)) hd⟩

end SepticProfile.PhysicalExterior

end
end

end OAI
