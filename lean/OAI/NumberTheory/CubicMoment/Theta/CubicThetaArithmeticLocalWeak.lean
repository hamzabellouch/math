import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalGreen
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticAxisRegularity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcingSmooth

namespace OAI

/-! The actual Eisenstein remainder satisfies the forced weak equation
against every compact C1 coordinate test at positive height. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaArithmetic_local_weak {s : ℂ} (hs : 2<s.re)
    (φ : ℂ × ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2}) :
    (∫ p, cubicThetaHeightInverse p*cubicThetaCoordinatePairing φ
      (fun q => cubicThetaArithmeticRemainder q s) p)+
      s*(s-2)*(∫ p, star (φ p)*cubicThetaArithmeticRemainder p s/(p.2:ℂ)^3)=
    ∫ p, star (φ p)*cubicThetaForcingSeries p s/(p.2:ℂ)^3 := by
  have hg := cubicThetaLocalGreen_identity φ (fun q => cubicThetaArithmeticRemainder q s)
    hφ hc hp (cubicThetaArithmeticRemainder_contDiffOn_one hs)
    (fun k => cubicThetaArithmetic_axisSecond_continuous k hs)
    (fun k p hp => cubicThetaArithmetic_axis_contDiffAt k hs hp)
  have hd : ContinuousOn (fun p : ℂ × ℝ => (p.2:ℂ)^3) {p : ℂ × ℝ | 0<p.2} :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn.pow 3
  have hn : ∀ p∈{p : ℂ × ℝ | 0<p.2}, (p.2:ℂ)^3≠0 :=
    fun p hp => pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hp.ne')
  have hM : Integrable (fun p => star (φ p)*cubicThetaArithmeticRemainder p s/(p.2:ℂ)^3) := by
    simpa only [mul_div_assoc,Pi.div_apply] using cubicThetaPositiveStarProduct_integrable hφ.continuous hc hp
      ((cubicThetaArithmeticRemainder_contDiffOn_one hs).continuousOn.div hd hn)
  have hF : Integrable (fun p => star (φ p)*cubicThetaForcingSeries p s/(p.2:ℂ)^3) := by
    simpa only [mul_div_assoc,Pi.div_apply] using cubicThetaPositiveStarProduct_integrable hφ.continuous hc hp
      ((cubicThetaForcingSeries_contDiffOn s).continuousOn.div hd hn)
  have he (p : ℂ × ℝ) :
      star (φ p)*cubicThetaCoordinateLaplacian (fun q => cubicThetaArithmeticRemainder q s) p/(p.2:ℂ)^3=
        s*(s-2)*(star (φ p)*cubicThetaArithmeticRemainder p s/(p.2:ℂ)^3)-
          star (φ p)*cubicThetaForcingSeries p s/(p.2:ℂ)^3 := by
    by_cases hpos : 0<p.2
    · have h := cubicThetaArithmeticRemainder_equation hs p.1.re p.1.im hpos
      rw [← cubicThetaCoordinateLaplacian_hyperbolic (fun q => cubicThetaArithmeticRemainder q s) p,
        cubicThetaCartesianPoint_self] at h
      have hl : cubicThetaCoordinateLaplacian (fun q => cubicThetaArithmeticRemainder q s) p=
          s*(s-2)*cubicThetaArithmeticRemainder p s-cubicThetaForcingSeries p s := by
        linear_combination h
      rw [hl]
      ring
    · have hz : φ p=0 := image_eq_zero_of_notMem_tsupport (fun h => hpos (hp h))
      simp only [hz,star_zero,zero_mul,zero_div,mul_zero,sub_self]
  have hi : (∫ p, star (φ p)*cubicThetaCoordinateLaplacian
      (fun q => cubicThetaArithmeticRemainder q s) p/(p.2:ℂ)^3)=
      s*(s-2)*(∫ p, star (φ p)*cubicThetaArithmeticRemainder p s/(p.2:ℂ)^3)-
        ∫ p, star (φ p)*cubicThetaForcingSeries p s/(p.2:ℂ)^3 := by
    simp_rw [he]
    rw [integral_sub (hM.const_mul _) hF,integral_const_mul]
  rw [hi] at hg
  linear_combination hg

end CubicFirstMoment

end

end OAI
