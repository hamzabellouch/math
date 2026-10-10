import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalVoronoi
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCubeCancellation

namespace OAI

/-! Exact free-cube denominator and transform argument in each actual
local dual term. The exponent 5/2 is derived, not assumed. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_norm_sqrt (d : Eisenstein) : ‖(d:ℂ)‖=Real.sqrt (norm d) := by
  rw [norm,Complex.normSq_eq_norm_sq,Real.sqrt_sq (_root_.norm_nonneg _)]

lemma cubicTheta_five_halves (d : Eisenstein) :
    norm d^(5/2:ℝ)=norm d*(Real.sqrt (norm d))^3 := by
  by_cases hd : d=0
  · subst d
    norm_num [norm]
  · rw [Real.sqrt_eq_rpow,←Real.rpow_mul_natCast (norm_nonneg d),
      show (5/2:ℝ)=1+(1/2:ℝ)*3 by norm_num,
      Real.rpow_add (norm_pos_of_ne_zero hd),Real.rpow_one]
    norm_num

lemma cubicThetaFrequency_cube_norm (n d : Eisenstein) :
    ‖cubicThetaFrequency (n*d^3)‖=‖cubicThetaFrequency n‖*(Real.sqrt (norm d))^3 := by
  rw [cubicThetaFrequency_mul_cube,norm_mul,norm_pow,cubicTheta_norm_sqrt]

lemma cubicThetaFrequency_cube_square (n d : Eisenstein) :
    ‖cubicThetaFrequency (n*d^3)‖^2=‖cubicThetaFrequency n‖^2*norm d^3 := by
  rw [cubicThetaFrequency_cube_norm,mul_pow,←pow_mul,
    show (3:ℕ)*2=2*3 by norm_num,pow_mul,Real.sq_sqrt (norm_nonneg d)]

theorem cubicThetaLocalDualTerm_cube {r d : Eisenstein} (hr : primary r)
    (hd : primary d) (hcop : IsCoprime d r) (n : MetaplecticDualArgument)
    (rev : Bool) (k : ℕ) (W : ℝ→ℂ) (σ X : ℝ) :
    cubicThetaLocalDualTerm r rev k W σ X (cubicThetaDualCube d hd n)=
      theta (cubicThetaCircleOrder rev k) (n.val*d^3)*
        (cubicThetaCommonTau n.val*metaplecticLocalCoefficient r n)/
          ((‖cubicThetaFrequency n.val‖^2*norm d^(5/2:ℝ):ℝ):ℂ)*
            metaplecticTransform (cubicThetaCircleOrder (!rev) k) W σ
              (cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2*norm d^3) := by
  have hn0 : (‖cubicThetaFrequency n.val‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (cubicThetaFrequency_pos n.property).ne'
  have hd0 : (norm d:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero (primary_ne_zero hd)).ne'
  have hds0 : (Real.sqrt (norm d):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hd))).ne'
  unfold cubicThetaLocalDualTerm
  rw [cubicThetaLocalCoefficient_cube hr hd hcop]
  dsimp only [cubicThetaDualCube]
  change theta _ (n.val*d^3)*
    (cubicThetaCommonCuspCoefficient (n.val*d^3)*metaplecticLocalCoefficient r n)/
      (‖cubicThetaFrequency (n.val*d^3)‖:ℂ)*_= _
  rw [cubicThetaCommonCuspCoefficient_primaryCube d hd,cubicThetaFrequency_cube_square,
    cubicThetaFrequency_cube_norm,cubicTheta_five_halves,cubicThetaCommonTau]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow]
  congr 1
  · field_simp
  · congr 1
    ring

end CubicFirstMoment

end

end OAI
