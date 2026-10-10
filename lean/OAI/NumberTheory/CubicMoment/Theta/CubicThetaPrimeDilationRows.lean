import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDilationCoordinates

namespace OAI

/-! Primitive-row branches of the actual prime dilation. These retain
both the common-prime branch and the cubic multiplier. -/
noncomputable section
namespace CubicFirstMoment

def CubicThetaBottomRow.primeNumerator {p : Eisenstein} (hp : primaryPrime p)
    (r : CubicThetaBottomRow) (hd : ¬p∣r.d) : CubicThetaBottomRow where
  c := p*r.c
  d := r.d
  c_three := dvd_mul_of_dvd_right r.c_three p
  d_primary := r.d_primary
  coprime := (hp.2.coprime_iff_not_dvd.mpr hd).mul_left r.coprime

def CubicThetaBottomRow.primeDenominator {p : Eisenstein} (hp : primary p)
    (r : CubicThetaBottomRow) (hd : p∣r.d) : CubicThetaBottomRow where
  c := r.c
  d := r.d/p
  c_three := r.c_three
  d_primary := primary_of_mul hp (by
    rw [EuclideanDomain.mul_div_cancel' (primary_ne_zero hp) hd]
    exact r.d_primary)
  coprime := r.coprime.of_isCoprime_of_dvd_right
    ⟨p,by rw [mul_comm,EuclideanDomain.mul_div_cancel' (primary_ne_zero hp) hd]⟩

lemma CubicThetaBottomRow.primeNumerator_phase {p : Eisenstein} (hp : primaryPrime p)
    (r : CubicThetaBottomRow) (hd : ¬p∣r.d) :
    (r.primeNumerator hp hd).phase=star (cubicSymbol p r.d)*r.phase := by
  change star (cubicSymbol r.d (p*r.c))=star (cubicSymbol p r.d)*star (cubicSymbol r.d r.c)
  rw [cubicSymbol_mul_upper r.d_primary,cubic_reciprocity r.d_primary hp.1,star_mul]
  ring

lemma CubicThetaBottomRow.primeDenominator_phase {p : Eisenstein} (hp : primary p)
    (r : CubicThetaBottomRow) (hd : p∣r.d) :
    r.phase=star (cubicSymbol p r.c)*(r.primeDenominator hp hd).phase := by
  have hd0 : r.d/p≠0 := by
    intro hz
    have he := EuclideanDomain.mul_div_cancel' (primary_ne_zero hp) hd
    rw [hz,mul_zero] at he
    exact primary_ne_zero r.d_primary he.symm
  change star (cubicSymbol r.d r.c)=star (cubicSymbol p r.c)*star (cubicSymbol (r.d/p) r.c)
  conv_lhs => rw [←EuclideanDomain.mul_div_cancel' (primary_ne_zero hp) hd]
  rw [cubicSymbol_mul_lower (primary_ne_zero hp) hd0,star_mul]
  ring

lemma CubicThetaBottomRow.primeNumerator_height {p : Eisenstein} (hp : primaryPrime p)
    (r : CubicThetaBottomRow) (hd : ¬p∣r.d) (z : ℂ × ℝ) :
    r.height (cubicThetaMobius (cubicThetaPrimeDilation hp.2.ne_zero) z)=
      ‖(p:ℂ)‖*(r.primeNumerator hp hd).height z := by
  rw [cubicThetaMobius_primeDilation]
  have hn : ‖(p:ℂ)‖^2=norm p := Complex.sq_norm _
  have he : (r.c:ℂ)*((p:ℂ)*z.1)+r.d=((p*r.c:Eisenstein):ℂ)*z.1+r.d := by
    push_cast
    ring
  change (‖(p:ℂ)‖*z.2)/(Complex.normSq ((r.c:ℂ)*((p:ℂ)*z.1)+r.d)+norm r.c*(‖(p:ℂ)‖*z.2)^2)=_
  rw [he,mul_pow,hn]
  change _=‖(p:ℂ)‖*(z.2/(Complex.normSq (((p*r.c:Eisenstein):ℂ)*z.1+r.d)+norm (p*r.c)*z.2^2))
  rw [norm_mul_eq]
  ring

end CubicFirstMoment

end

end OAI
