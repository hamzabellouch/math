import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLevelTransformation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScaledUpperMellin

namespace OAI

/-! Put the genuine primary-level theta transformation on a symmetric
height scale, before Mellin integration. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaLevelScale (q : Eisenstein) : ℝ := (Real.sqrt (norm q))⁻¹

lemma cubicThetaLevelScale_pos {q : Eisenstein} (hq : primary q) :
    0<cubicThetaLevelScale q :=
  inv_pos.mpr (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hq)))

lemma cubicThetaLevelScale_reciprocal {q : Eisenstein} (hq : primary q)
    {t : ℝ} (ht : 0<t) :
    (norm q*(cubicThetaLevelScale q*t))⁻¹=cubicThetaLevelScale q*t⁻¹ := by
  have hN := norm_pos_of_ne_zero (primary_ne_zero hq)
  have hs := Real.sqrt_pos.mpr hN
  have hs2 := Real.sq_sqrt hN.le
  unfold cubicThetaLevelScale
  field_simp
  nlinarith

def cubicThetaLevelConstant (q : Eisenstein) : ℂ :=
  cubicThetaSeriesConstant*((cubicThetaLevelScale q^(2/3:ℝ):ℝ):ℂ)

theorem cubicThetaLevelAxis_reciprocity {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) {t : ℝ} (ht : 0<t) :
    cubicThetaScaledAxis (3*(y:ℂ)/(q:ℂ)) (cubicThetaLevelScale q) t⁻¹=
      cubicSymbol q (3*y)*
        cubicThetaScaledAxis (-3*(x:ℂ)/(q:ℂ)) (cubicThetaLevelScale q) t+
      cubicThetaLevelConstant q*(cubicSymbol q (3*y)*((t^(2/3:ℝ):ℝ):ℂ)-
        (((t⁻¹)^(2/3:ℝ):ℝ):ℂ)) := by
  have hr := cubicThetaLevelScale_pos hq
  have he := cubicThetaArithmetic_rational_inversion hq x y hxy (mul_pos hr ht)
  rw [cubicThetaLevelScale_reciprocal hq ht,
    Real.mul_rpow hr.le ht.le,Real.mul_rpow hr.le (inv_nonneg.mpr ht.le)] at he
  change _=_ at he
  simp only [Complex.ofReal_mul] at he
  unfold cubicThetaScaledAxis cubicThetaLevelConstant
  linear_combination he

end CubicFirstMoment

end

end OAI
