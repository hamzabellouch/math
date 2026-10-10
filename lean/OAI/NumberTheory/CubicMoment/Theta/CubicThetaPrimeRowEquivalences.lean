import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDilationRows

namespace OAI

/-! Exact primitive-row bijections for the two branches of prime dilation. -/
noncomputable section
namespace CubicFirstMoment

lemma CubicThetaBottomRow.prime_not_dvd_d {p : Eisenstein} (hp : primaryPrime p)
    (r : CubicThetaBottomRow) (hc : p∣r.c) : ¬p∣r.d :=
  fun hd => hp.2.not_isUnit (r.coprime.isRelPrime hc hd)

def CubicThetaBottomRow.primeNumeratorInverse {p : Eisenstein} (hp : primary p)
    (r : CubicThetaBottomRow) (hc : p∣r.c) : CubicThetaBottomRow where
  c := r.c/p
  d := r.d
  c_three := (primary_coprime_three hp).symm.dvd_of_dvd_mul_left
    (by rw [EuclideanDomain.mul_div_cancel' (primary_ne_zero hp) hc]; exact r.c_three)
  d_primary := r.d_primary
  coprime := r.coprime.of_isCoprime_of_dvd_left (EuclideanDomain.div_dvd_of_dvd hc)

def CubicThetaBottomRow.primeDenominatorInverse {p : Eisenstein} (hp : primaryPrime p)
    (r : CubicThetaBottomRow) (hc : ¬p∣r.c) : CubicThetaBottomRow where
  c := r.c
  d := p*r.d
  c_three := r.c_three
  d_primary := primary_mul hp.1 r.d_primary
  coprime := (hp.2.coprime_iff_not_dvd.mpr hc).symm.mul_right r.coprime

def cubicThetaPrimeNumeratorRowEquiv {p : Eisenstein} (hp : primaryPrime p) :
    {r : CubicThetaBottomRow // ¬p∣r.d} ≃ {r : CubicThetaBottomRow // p∣r.c} where
  toFun r := ⟨r.val.primeNumerator hp r.property,dvd_mul_right _ _⟩
  invFun r := ⟨r.val.primeNumeratorInverse hp.1 r.property,
    r.val.prime_not_dvd_d hp r.property⟩
  left_inv r := by
    apply Subtype.ext
    apply CubicThetaBottomRow.ext
    · exact mul_div_cancel_left₀ r.val.c hp.2.ne_zero
    · rfl
  right_inv r := by
    apply Subtype.ext
    apply CubicThetaBottomRow.ext
    · exact EuclideanDomain.mul_div_cancel' hp.2.ne_zero r.property
    · rfl

def cubicThetaPrimeDenominatorRowEquiv {p : Eisenstein} (hp : primaryPrime p) :
    {r : CubicThetaBottomRow // p∣r.d} ≃ {r : CubicThetaBottomRow // ¬p∣r.c} where
  toFun r := ⟨r.val.primeDenominator hp.1 r.property,
    fun hc => hp.2.not_isUnit (r.val.coprime.isRelPrime hc r.property)⟩
  invFun r := ⟨r.val.primeDenominatorInverse hp r.property,dvd_mul_right _ _⟩
  left_inv r := by
    apply Subtype.ext
    apply CubicThetaBottomRow.ext
    · rfl
    · exact EuclideanDomain.mul_div_cancel' hp.2.ne_zero r.property
  right_inv r := by
    apply Subtype.ext
    apply CubicThetaBottomRow.ext
    · rfl
    · exact mul_div_cancel_left₀ r.val.d hp.2.ne_zero

end CubicFirstMoment

end

end OAI
