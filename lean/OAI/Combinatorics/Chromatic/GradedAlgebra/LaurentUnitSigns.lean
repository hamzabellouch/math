import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentSigns

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]
lemma negative_unit_rat (n : ℤ) :
    ((-1 : (LaurentSeries R)ˣ)^n).val=C (algebraMap ℚ R ((-1 : ℚ)^n)) := by
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast,zpow_natCast,Units.val_pow_eq_pow_val,Units.val_neg,
      Units.val_one,map_pow,map_neg,map_one]
  | negSucc n =>
    rw [zpow_negSucc,←inv_pow,ElementaryPositivity.unit_neg_one_inv]
    simp only [Units.val_pow_eq_pow_val,Units.val_neg,Units.val_one,zpow_negSucc,
      ←inv_pow,inv_neg,inv_one,map_pow,map_neg,map_one]
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
