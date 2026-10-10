import Mathlib
import OAI.Analysis.FreeWords.PartialUnitaryAlgebra

namespace OAI

noncomputable section

namespace KKLocalPatching.PartialUnitary

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

theorem norm_support_le_one (v : PartialUnitary A) : ‖v.support‖≤1 := by
  have h := CStarRing.norm_star_mul_self (x := v.support)
  rw [v.projection.isSelfAdjoint.star_eq,v.projection.isIdempotentElem.eq] at h
  nlinarith [norm_nonneg v.support]

theorem norm_power_le_one (v : PartialUnitary A) (k : ℤ) : ‖v.power k‖≤1 := by
  have h := CStarRing.norm_star_mul_self (x := v.power k)
  rw [v.star_power_mul] at h
  nlinarith [v.norm_support_le_one,norm_nonneg (v.power k)]

end KKLocalPatching.PartialUnitary
end

end OAI
