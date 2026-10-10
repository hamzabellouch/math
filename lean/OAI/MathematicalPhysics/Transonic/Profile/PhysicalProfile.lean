import OAI.MathematicalPhysics.Transonic.Profile.Equations

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set Filter
open scoped Topology ContDiff

lemma inverse_profile_equation {ell beta y U m : ℝ}
    (hden : 1-y*U≠0)
    (hode : sonicDenom ell y U*m=sonicNumer ell beta y U) :
    profileDenom ell y (velocityToU y U)*
      ((1-U^2-(1-y^2)*m)/(1-y*U)^2)=
      profileNumer ell beta y (velocityToU y U) := by
  dsimp [sonicDenom,sonicNumer] at hode
  dsimp [profileDenom,profileNumer,velocityToU]
  field_simp
  linear_combination -(1-y^2)^2*hode

lemma velocityToU_involutive {y U : ℝ} (hy : 1-y^2≠0) (hd : 1-y*U≠0) :
    velocityToU y (velocityToU y U)=U := by
  unfold velocityToU
  have hh : 1-y*((y-U)/(1-y*U))=(1-y^2)/(1-y*U) := by field_simp;ring
  rw [hh]
  field_simp
  ring

lemma velocityToU_range {y U : ℝ} (hy : |y|<1) (hU : |U|<1) :
    |velocityToU y U|<1 := by
  have hy' := abs_lt.mp hy
  have hU' := abs_lt.mp hU
  have hd : 0<1-y*U := by
    have hmul : |y*U|<1 := by
      rw [abs_mul]
      calc
        |y| * |U| ≤ 1 * |U| := mul_le_mul_of_nonneg_right hy.le (abs_nonneg _)
        _ < 1 := by simpa using hU
    linarith [(abs_lt.mp hmul).2]
  rw [abs_lt,velocityToU]
  constructor
  · apply (lt_div_iff₀ hd).mpr
    nlinarith [mul_pos (by linarith : 0<1+y) (by linarith : 0<1-U)]
  · apply (div_lt_iff₀ hd).mpr
    nlinarith [mul_pos (by linarith : 0<1-y) (by linarith : 0<1+U)]

lemma velocityToU_below {y U : ℝ} (hy : |y|<1) (hU : 0<U) (hd : 0<1-y*U) :
    velocityToU y U<y := by
  rw [velocityToU,div_lt_iff₀ hd]
  have hs : 0<1-y^2 := by
    have := abs_lt.mp hy
    nlinarith [sq_nonneg y]
  nlinarith [mul_pos hs hU]


end SepticProfile

end
end

end OAI
