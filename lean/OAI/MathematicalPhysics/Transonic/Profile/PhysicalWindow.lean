import OAI.MathematicalPhysics.Transonic.Profile.PhysicalEntry
import OAI.MathematicalPhysics.Transonic.Exterior.WindowSound

namespace OAI

section
noncomputable section
namespace SepticProfile.PhysicalExterior
open Set SourceFamily ExteriorPolynomial SonicShooting
open scoped ContDiff

lemma sonicSpeed_sqrt : sonicSpeed*Real.sqrt (5/3)=1 := by
  unfold sonicSpeed ell
  exact one_div_mul_cancel (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

lemma scaled_abs {v : ℝ} (hv : 0<v ∧ v<Real.sqrt (5/3)) : |sonicSpeed*v|<1 := by
  rw [abs_of_pos (mul_pos sonicSpeed_bounds.1 hv.1)]
  simpa only [sonicSpeed_sqrt] using mul_lt_mul_of_pos_left hv.2 sonicSpeed_bounds.1

lemma window_endpoint {p : Parameter} {d : ℝ} {u : PowerSeries ℝ}
    (W : AdmissibleWindow (sig p) (kap p) d u) :
    0<sonicRadius (ShootingParameters.beta p.val)*(1+d/256) ∧
    sonicRadius (ShootingParameters.beta p.val)*(1+d/256)<1 := by
  have hb := ShootingParameters.standing_beta_bound p.property
  have hr := (source_parameter_bounds hb.1 hb.2).2.2.2.2.1
  have hp : 0<sonicRadius (ShootingParameters.beta p.val)*(1+d/256) :=
    mul_pos hr (by linarith [div_pos W.dpos (by norm_num : (0:ℝ)<256)])
  refine ⟨hp,?_⟩
  have hs := W.subsonic
  rw [← source_sigma p,sigma_eq_radius_sq (ne_of_gt (source_q_pos p))] at hs
  nlinarith

lemma window_global {p : Parameter} {d ue : ℝ} {u : PowerSeries ℝ}
    (W : AdmissibleWindow (sig p) (kap p) d u)
    (he : (lowerPoly u d).eval 1≤ue) (heu : ue<Real.sqrt (5/3)) :
    let beta := ShootingParameters.beta p.val
    let a := sonicRadius beta*(1+d/256)
    let m := velocityToU a (sonicSpeed*(lowerPoly u d).eval 1)
    ∃ v : ℝ → ℝ, v a=velocityToU a (sonicSpeed*ue) ∧
      (∀ y∈Ici a, -1<v y ∧ v y≤ m) ∧
      (∀ y∈Ici a, HasDerivWithinAt v (field ell beta (y,v y)) (Ici a) y) ∧
      ContDiffOn ℝ ∞ v (Ici a) ∧
      (∀ y∈Ici a, v y<y ∧ y*v y<1) := by
  dsimp only
  let beta := ShootingParameters.beta p.val
  let a := sonicRadius beta*(1+d/256)
  let P := (lowerPoly u d).eval 1
  let m := velocityToU a (sonicSpeed*P)
  have hb := ShootingParameters.standing_beta_bound p.property
  have ha : 0<a ∧ a<1 := window_endpoint W
  have hy : |a|<1 := by rw [abs_of_pos ha.1];exact ha.2
  have hP : 1<P ∧ P<6/5 := W.range 1 ⟨by norm_num,le_rfl⟩
  have hq : (6/5:ℝ)<Real.sqrt (5/3) := by
    have he := Real.sq_sqrt (by norm_num : (0:ℝ)≤5/3)
    have hn := Real.sqrt_nonneg (5/3:ℝ)
    nlinarith
  have hU : |sonicSpeed*P|<1 := scaled_abs ⟨by linarith [hP.1],hP.2.trans hq⟩
  have hUE : |sonicSpeed*ue|<1 := scaled_abs ⟨by linarith [hP.1],heu⟩
  have hpos (v:ℝ) (hv:|sonicSpeed*v|<1) : 0<1-a*(sonicSpeed*v) := by
    have hu := (abs_lt.mp hv).2
    nlinarith [mul_nonneg ha.1.le (sub_nonneg.mpr hu.le)]
  have hm : -1< m ∧ m<1 := abs_lt.mp (velocityToU_range hy hU)
  have hfirst := sonic_exit_factors hy hU hP.1
  have hcrit : 0<beta*ell*(1-m^2)*a-3*m*(1-a*m) := by
    apply critical_exit hb.1 hb.2 rfl hy hU
    simpa only [beta,source_kappa] using W.exit
  have hstart : -1<velocityToU a (sonicSpeed*ue) ∧ velocityToU a (sonicSpeed*ue)≤ m := by
    refine ⟨(abs_lt.mp (velocityToU_range hy hUE)).1,?_⟩
    exact chart_antitone hy (hpos P hU) (hpos ue hUE)
      (mul_le_mul_of_nonneg_left he sonicSpeed_bounds.1.le)
  have hqs : 1<Real.sqrt ell := by
    change 1<Real.sqrt (5/3)
    linarith
  have hsq : (Real.sqrt ell)^2=ell := Real.sq_sqrt (by norm_num [ell])
  obtain ⟨v,hv,hvr,hvd⟩ := global_continuation (beta:=beta) hqs (by linarith [hb.1]) ha.1
    hm hfirst.1 hfirst.2 (by simpa only [hsq] using hcrit) hstart
  have hvs := solution_smooth hqs ha.1 hm hfirst.1 hfirst.2 hvr hvd
  have hrec := solution_below_reciprocal hqs hb.1 ha.2 hm.2
    (fun y hy => (hvr y hy).2) hvd
  refine ⟨v,hv,hvr,?_,?_,?_⟩
  · simpa only [hsq] using hvd
  · simpa only [hsq] using hvs
  · intro y hy
    have hma : m<a := velocityToU_below (show |a|<1 from by rw [abs_of_pos ha.1];exact ha.2) (mul_pos sonicSpeed_bounds.1 (by linarith [hP.1])) (hpos P hU)
    constructor
    · exact ((hvr y hy).2.trans_lt hma).trans_le hy
    · by_cases hy1 : 1≤y
      · have hh := mul_lt_mul_of_pos_left (hrec y hy1) (by linarith : 0<y)
        simpa only [mul_one_div_cancel (by linarith : y≠0)] using hh
      · have hv1 := ((hvr y hy).2).trans_lt hm.2
        have hyp : 0<y := ha.1.trans_le hy
        nlinarith [mul_nonneg hyp.le (sub_nonneg.mpr hv1.le)]

end SepticProfile.PhysicalExterior

end
end

end OAI
