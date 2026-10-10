import Mathlib
import OAI.Analysis.FreeWords.PartialIsoAlgebra

namespace OAI

noncomputable section

namespace KKProjectionSupport

noncomputable section

variable {A : Type*} [CStarAlgebra A]

end

end KKProjectionSupport

namespace KKProjectionSupport

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem projection_sub {p e : A} (hp : IsStarProjection p) (he : IsStarProjection e)
    (hep : e*p=e) : IsStarProjection (p-e) := by
  have hpe : p*e=e := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq, he.isSelfAdjoint.star_eq] using congrArg star hep
  constructor
  · change (p-e)*(p-e)=p-e
    rw [sub_mul, mul_sub, mul_sub, hp.isIdempotentElem.eq, he.isIdempotentElem.eq, hep, hpe]
    abel
  · change star (p-e)=p-e
    rw [star_sub, hp.isSelfAdjoint.star_eq, he.isSelfAdjoint.star_eq]

theorem initial_bound {v p : A} (hp : IsStarProjection p) (hvp : v*p=v) :
    (star v*v)*p=star v*v ∧ p*(star v*v)=star v*v := by
  have h : (star v*v)*p=star v*v := by rw [mul_assoc, hvp]
  exact ⟨h, by simpa only [star_mul, star_star, hp.isSelfAdjoint.star_eq] using congrArg star h⟩

theorem final_bound {v q : A} (hq : IsStarProjection q) (hqv : q*v=v) :
    (v*star v)*q=v*star v ∧ q*(v*star v)=v*star v := by
  have h : q*(v*star v)=v*star v := by rw [← mul_assoc, hqv]
  exact ⟨by simpa only [star_mul, star_star, hq.isSelfAdjoint.star_eq] using congrArg star h, h⟩

theorem partial_add_orthogonal {v w : A} (hv : Partial v) (hw : Partial w)
    (hvw : star v*w=0) (hvsw : v*star w=0) :
    Partial (v+w) ∧ Extends v (v+w) := by
  have hwv : star w*v=0 := by simpa only [star_mul, star_star, star_zero] using congrArg star hvw
  have hwsv : w*star v=0 := by simpa only [star_mul, star_star, star_zero] using congrArg star hvsw
  have hs : star (v+w)*(v+w)=star v*v+star w*w := by
    rw [star_add, add_mul, mul_add, mul_add, hvw, hwv, zero_add, add_zero]
  constructor
  · change (v+w)*star (v+w)*(v+w)=v+w
    rw [mul_assoc, hs, add_mul, mul_add, mul_add, ← mul_assoc v (star w), hvsw,
      ← mul_assoc w (star v), hwsv, zero_mul, zero_mul, add_zero, zero_add]
    rw [← mul_assoc, ← mul_assoc, hv, hw]
  · constructor
    · rw [add_mul, ← mul_assoc, hv, ← mul_assoc, hwsv, zero_mul, add_zero]
    · rw [mul_add, hvw, add_zero]

theorem orthogonal_of_residual {v w p q : A} (hv : Partial v)
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hvp : v*p=v) (hqv : q*v=v)
    (hwp : w*(p-star v*v)=w) (hqw : (q-v*star v)*w=w) :
    star v*w=0 ∧ v*star w=0 := by
  have hs : star v*q=star v := by
    simpa only [star_mul, hq.isSelfAdjoint.star_eq] using congrArg star hqv
  have hs0 : star v*(q-v*star v)=0 := by
    have hvs : star v*v*star v=star v := by
      simpa only [Partial, star_star] using partial_star hv
    rw [mul_sub, hs, ← mul_assoc, hvs, sub_self]
  have h0 : v*(p-star v*v)=0 := by
    rw [mul_sub, hvp, ← mul_assoc, hv, sub_self]
  constructor
  · calc
      star v*w=star v*((q-v*star v)*w) := by rw [hqw]
      _=0 := by rw [← mul_assoc, hs0, zero_mul]
  · have hsw : (p-star v*v)*star w=star w := by
      simpa only [star_mul, star_sub, star_star, hp.isSelfAdjoint.star_eq] using congrArg star hwp
    calc
      v*star w=v*((p-star v*v)*star w) := by rw [hsw]
      _=0 := by rw [← mul_assoc, h0, zero_mul]

end

end KKProjectionSupport
end

end OAI
