import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordCoefficientAgreement
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteLogCoefficientBound

namespace OAI

/-! # Stable coefficients of a finite logarithm in the augmentation ideal -/

noncomputable section
namespace PolycyclicRecognition

theorem finiteNilpotentLog_succ {A : Type*} [Ring A] [Algebra ℚ A] (p : A) (c : ℕ) :
    finiteNilpotentLog (c + 2) p = finiteNilpotentLog (c + 1) p +
      ((-1 : ℚ) ^ (c + 2) / (c + 1)) • p ^ (c + 1) := by
  rw [show c + 2 = (c + 1) + 1 from rfl, finiteNilpotentLog_sum, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [← finiteNilpotentLog_sum]

theorem WordCoefficientAgreement.finiteLog {n k : ℕ} {p q : RationalWords n}
    (h : WordCoefficientAgreement p q k) (c : ℕ) :
    WordCoefficientAgreement (finiteNilpotentLog (c + 1) p)
      (finiteNilpotentLog (c + 1) q) k := by
  intro w hw
  rw [finiteNilpotentLog_sum, finiteNilpotentLog_sum]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul, Finsupp.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [h.pow (i.val + 1) w hw]

theorem finiteLog_coefficient_stable {c d n : ℕ} (h : c ≤ d)
    (p : RationalWords n) (hp : p.coeff 1 = 0)
    (w : FreeMonoid (Fin n)) (hw : w.length ≤ c) :
    (finiteNilpotentLog (c + 1) p).coeff w = (finiteNilpotentLog (d + 1) p).coeff w := by
  induction d, h using Nat.le_induction with
  | base => rfl
  | succ d h ih =>
    rw [show d + 1 + 1 = d + 2 from rfl, finiteNilpotentLog_succ]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply,
      MonoidAlgebra.coeff_smul, Finsupp.smul_apply]
    rw [wordMinimumDegree_pow hp (d + 1) w (by omega), smul_zero, add_zero]
    exact ih

end PolycyclicRecognition

end

end OAI
