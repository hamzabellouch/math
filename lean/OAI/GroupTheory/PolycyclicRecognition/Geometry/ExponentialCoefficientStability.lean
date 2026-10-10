import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordCoefficientAgreement
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialProductCoefficients

namespace OAI

/-! # Stable low-degree coefficients of the universal exponential product -/

noncomputable section
namespace PolycyclicRecognition

theorem freeMonoid_length_pow {I : Type*} (w : FreeMonoid I) (k : ℕ) :
    (w ^ k).length = k * w.length := by
  induction k with
  | zero => simp only [pow_zero, FreeMonoid.length_one, Nat.zero_mul]
  | succ k ih => rw [pow_succ, FreeMonoid.length_mul, ih, Nat.succ_mul]

theorem rationalWordExponential_succ (c n : ℕ) (i : Fin n) :
    rationalWordExponential (c + 1) n i = rationalWordExponential c n i +
      MonoidAlgebra.single (FreeMonoid.of i ^ (c + 1)) (((c + 1).factorial : ℚ)⁻¹) := by
  rw [rationalWordExponential_sum, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [← rationalWordExponential_sum]

theorem rationalWordExponential_coefficient_stable {c d n : ℕ} (h : c ≤ d)
    (i : Fin n) (w : FreeMonoid (Fin n)) (hw : w.length ≤ c) :
    (rationalWordExponential c n i).coeff w = (rationalWordExponential d n i).coeff w := by
  classical
  induction d, h using Nat.le_induction with
  | base => rfl
  | succ d h ih =>
    rw [rationalWordExponential_succ, MonoidAlgebra.coeff_add, Finsupp.add_apply]
    have hne : FreeMonoid.of i ^ (d + 1) ≠ w := by
      intro he
      have hh := congrArg FreeMonoid.length he
      simp only [freeMonoid_length_pow, FreeMonoid.length_of, mul_one] at hh
      omega
    rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hne.symm, add_zero]
    exact ih

theorem rationalExponentialProduct_coefficient_stable {c d n : ℕ} (h : c ≤ d) :
    WordCoefficientAgreement (rationalExponentialProduct c n)
      (rationalExponentialProduct d n) (c + 1) := by
  apply wordCoefficientAgreement_ofFn_prod
  intro i w hw
  exact rationalWordExponential_coefficient_stable h i w (by omega)

end PolycyclicRecognition

end

end OAI
