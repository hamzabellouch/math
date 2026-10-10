import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLevelAngular
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLevelReciprocity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScaledAngularMellin

namespace OAI

/-! Put every genuine signed angular transformation on the symmetric height scale. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaLevelAngularRoot (q : Eisenstein) (rev : Bool) (k : ℕ) : ℂ :=
  (cubicThetaCircleMultiplier (!rev) (-(norm q:ℂ)/(q:ℂ)^2))^k

lemma cubicThetaLevelScale_square (q : Eisenstein) :
    cubicThetaLevelScale q^2=(norm q)⁻¹ := by
  unfold cubicThetaLevelScale
  rw [inv_pow,Real.sq_sqrt (norm_nonneg q)]

lemma cubicThetaLevelAngular_scaled_direction {q : Eisenstein} (hq : primary q)
    {t : ℝ} (ht : 0<t) :
    -1/((q:ℂ)^2*((cubicThetaLevelScale q*t⁻¹:ℝ):ℂ)^2)=
      (-(norm q:ℂ)/(q:ℂ)^2)*(t:ℂ)^2 := by
  have hqC : (q:ℂ)≠0 := fun he => primary_ne_zero hq (Subtype.ext he)
  have hN : (norm q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_pos_of_ne_zero (primary_ne_zero hq)).ne'
  have htC : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hs : (cubicThetaLevelScale q:ℂ)^2=(norm q:ℂ)⁻¹ := by
    exact_mod_cast cubicThetaLevelScale_square q
  simp only [Complex.ofReal_mul,Complex.ofReal_inv,mul_pow,hs]
  field_simp [hqC,hN,htC]

lemma cubicThetaCircleMultiplier_real_mul (rev : Bool) (d : ℂ) (t : ℝ) :
    cubicThetaCircleMultiplier rev (d*(t:ℂ)^2)=
      cubicThetaCircleMultiplier rev d*(t:ℂ)^2 := by
  cases rev <;> simp [cubicThetaCircleMultiplier,star_mul,mul_comm]

theorem cubicThetaLevelAngularAxis_reciprocity {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) (rev : Bool) {k : ℕ} (hk : 0<k)
    {t : ℝ} (ht : 0<t) :
    cubicSymbol q (3*y)*cubicThetaScaledAngularAxis (cubicThetaCircleOrder rev k)
      (-(3*(x:ℂ)/(q:ℂ))) (cubicThetaLevelScale q) (1/t)=
    cubicThetaLevelAngularRoot q rev k*(t:ℂ)^(2*k)*
      cubicThetaScaledAngularAxis (cubicThetaCircleOrder (!rev) k)
        (3*(y:ℂ)/(q:ℂ)) (cubicThetaLevelScale q) t := by
  have hv := mul_pos (cubicThetaLevelScale_pos hq) (inv_pos.mpr ht)
  have H := cubicThetaArithmetic_level_angular hq x y hxy hv rev hk
  rw [cubicThetaLevelScale_reciprocal hq (inv_pos.mpr ht),inv_inv,
    cubicThetaLevelAngular_scaled_direction hq ht,cubicThetaCircleMultiplier_real_mul] at H
  simpa only [cubicThetaScaledAngularAxis,cubicThetaLevelAngularRoot,one_div,mul_pow,pow_mul,
    mul_assoc] using H

end CubicFirstMoment

end

end OAI
