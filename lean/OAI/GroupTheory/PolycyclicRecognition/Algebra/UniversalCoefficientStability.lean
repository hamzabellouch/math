import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialCoefficientStability
import OAI.GroupTheory.PolycyclicRecognition.Algebra.LogarithmCoefficientStability
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundedAssociativeBCH

namespace OAI

/-! # Independence of the low-degree universal BCH coefficients

Increasing the finite exponential and logarithm truncations changes only
higher word degrees. Thus the universal coefficients can be restricted to
the actual nilpotency class.
-/

noncomputable section
namespace PolycyclicRecognition

theorem rationalUniversalLogarithm_stable {c d n : ℕ} (h : c ≤ d) :
    WordCoefficientAgreement (rationalUniversalLogarithm c n)
      (rationalUniversalLogarithm d n) (c + 1) := by
  have hp := (rationalExponentialProduct_coefficient_stable (n := n) h).sub
    (WordCoefficientAgreement.refl 1 (c + 1))
  intro w hw
  exact (hp.finiteLog c w hw).trans
    (finiteLog_coefficient_stable h (rationalExponentialProduct d n - 1)
      (rationalExponentialProduct_sub_one_empty d n) w (by omega))

theorem universalLogarithmCoefficient_stable {c d n e : ℕ} (h : c ≤ d) (he : e ≤ c) :
    universalLogarithmCoefficient c n e = universalLogarithmCoefficient d n e := by
  ext w
  rw [universalLogarithmCoefficient_coeff he,
    universalLogarithmCoefficient_coeff (he.trans h)]
  by_cases hw : w.length = e
  · rw [ite_eq_left hw, ite_eq_left hw]
    exact rationalUniversalLogarithm_stable h w (by omega)
  · rw [ite_eq_right hw, ite_eq_right hw]

theorem universalDynkinCoefficients_stable {c d n : ℕ} (h : c ≤ d)
    (e : Fin c) (w : Fin (e.val + 1) → Fin n) :
    universalDynkinCoefficients c n e w =
      universalDynkinCoefficients d n (e.castLE h) w := by
  unfold universalDynkinCoefficients
  simp only [Fin.val_castLE]
  rw [universalLogarithmCoefficient_stable h (Nat.succ_le_of_lt e.isLt)]

end PolycyclicRecognition

end

end OAI
