import OAI.MathematicalPhysics.Transonic.Profile.ExteriorBranch

namespace OAI

section
noncomputable section
namespace SepticProfile.PhysicalExterior
open Set SourceFamily ExteriorPolynomial SonicShooting

lemma window_strip_den_ne {p : Parameter} {d y v : ℝ} {u : PowerSeries ℝ}
    (W : AdmissibleWindow (sig p) (kap p) d u)
    (hy : sonicRadius (ShootingParameters.beta p.val)*(1+d/256)≤y)
    (hv : -1≤v ∧ v≤velocityToU (sonicRadius (ShootingParameters.beta p.val)*(1+d/256))
      (sonicSpeed*(lowerPoly u d).eval 1)) : profileDenom ell y v≠0 := by
  let a := sonicRadius (ShootingParameters.beta p.val)*(1+d/256)
  let P := (lowerPoly u d).eval 1
  let m := velocityToU a (sonicSpeed*P)
  have ha : 0<a ∧ a<1 := window_endpoint W
  have hay : |a|<1 := by rw [abs_of_pos ha.1];exact ha.2
  have hP : 1<P ∧ P<6/5 := W.range 1 ⟨by norm_num,le_rfl⟩
  have hq : (6/5:ℝ)<Real.sqrt (5/3) := by
    have he := Real.sq_sqrt (by norm_num : (0:ℝ)≤5/3)
    nlinarith only [he,Real.sqrt_nonneg (5/3:ℝ)]
  have hU : |sonicSpeed*P|<1 := scaled_abs ⟨by linarith only [hP.1],hP.2.trans hq⟩
  have hm : -1< m ∧ m<1 := abs_lt.mp (velocityToU_range hay hU)
  have hf := sonic_exit_factors hay hU hP.1
  have hqs : 1<Real.sqrt ell := by change 1<Real.sqrt (5/3);linarith only [hq]
  have hn := denominator_neg hqs ha.1 hm hf.1 hf.2 hy hv
  rw [Real.sq_sqrt (by norm_num [ell] : (0:ℝ)≤ell)] at hn
  exact ne_of_lt hn

lemma denom_zero_of_sonic {y v : ℝ} (hp : 1-y*v≠0)
    (h : velocityToU y v=sonicSpeed) : profileDenom ell y v=0 := by
  have hs : ell*sonicSpeed^2=1 := by rw [sonicSpeed_sq];norm_num [ell]
  have he : y-v=sonicSpeed*(1-y*v) := (div_eq_iff hp).mp h
  have he' : v-y= -sonicSpeed*(1-y*v) := by linarith only [he]
  have he2 : ell*(v-y)^2=(1-y*v)^2 := by
    rw [he']
    calc
      _=(ell*sonicSpeed^2)*(1-y*v)^2 := by ring
      _=(1-y*v)^2 := by rw [hs,one_mul]
  simp only [profileDenom,he2,sub_self,mul_zero]

end SepticProfile.PhysicalExterior

end
end

end OAI
