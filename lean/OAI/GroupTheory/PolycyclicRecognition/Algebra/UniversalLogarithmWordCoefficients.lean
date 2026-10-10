import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalUniversalLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedWordComponents

namespace OAI

/-! # Rational coefficients of the universal logarithm -/

noncomputable section
namespace PolycyclicRecognition

variable {c n d : ℕ}

theorem rationalWordWeight_coefficient (p : RationalWords n) (hd : d ≤ c)
    (w : FreeMonoid (Fin n)) :
    (monoidCoefficientLinear (truncatedScalarCoefficient c d) (rationalWordWeight c n p)).coeff w =
      if w.length = d then p.coeff w else 0 := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
    split_ifs <;> simp
  | single v q =>
    rw [rationalWordWeight_single, map_smul, weightedWord_coefficient v hd]
    by_cases hvw : v = w
    · subst v
      by_cases hw : w.length = d <;> simp [hw]
    · by_cases hv : v.length = d <;> simp [hv, MonoidAlgebra.coeff_single, hvw]

theorem universalLogarithmCoefficient_coeff (hd : d ≤ c) (w : FreeMonoid (Fin n)) :
    (universalLogarithmCoefficient c n d).coeff w =
      if w.length = d then (rationalUniversalLogarithm c n).coeff w else 0 := by
  rw [universalLogarithmCoefficient, ← rationalWordWeight_universalLogarithm]
  exact rationalWordWeight_coefficient _ hd w

end PolycyclicRecognition

end

end OAI
