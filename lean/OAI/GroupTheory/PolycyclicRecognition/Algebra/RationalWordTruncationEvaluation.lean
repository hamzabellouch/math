import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniversalLogarithmWordCoefficients

namespace OAI

/-! # Evaluation through finitely many homogeneous word degrees -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {A : Type*} [Ring A] [Algebra ℚ A] {c n : ℕ} (X : Fin n → A)

theorem rationalWordWeight_single_component (w : FreeMonoid (Fin n)) (q : ℚ) (d : ℕ)
    (hd : d ≤ c) :
    monoidCoefficientLinear (truncatedScalarCoefficient c d)
      (rationalWordWeight c n (MonoidAlgebra.single w q)) =
      if w.length = d then MonoidAlgebra.single w q else 0 := by
  rw [rationalWordWeight_single, map_smul, weightedWord_coefficient w hd]
  split_ifs <;> simp [MonoidAlgebra.smul_single, smul_eq_mul]

theorem rationalWord_evaluation_by_degrees
    (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0)
    (p : RationalWords n) :
    rationalWordEvaluation X p = ∑ d : Fin (c + 1), rationalWordEvaluation X
      (monoidCoefficientLinear (truncatedScalarCoefficient c d.val) (rationalWordWeight c n p)) := by
  classical
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, Finset.sum_add_distrib, hp, hq]
  | single w q =>
    have hd (d : Fin (c + 1)) : rationalWordEvaluation X
        (monoidCoefficientLinear (truncatedScalarCoefficient c d.val)
          (rationalWordWeight c n (MonoidAlgebra.single w q))) =
        if w.length = d.val then q • FreeMonoid.lift X w else 0 := by
      rw [rationalWordWeight_single_component w q d.val (Nat.le_of_lt_succ d.isLt)]
      split_ifs <;> simp only [rationalWordEvaluation_single, ← FreeMonoid.lift_apply, map_zero]
    rw [rationalWordEvaluation_single, ← FreeMonoid.lift_apply]
    simp_rw [hd]
    by_cases hw : w.length ≤ c
    · let k : Fin (c + 1) := ⟨w.length, Nat.lt_succ_of_le hw⟩
      have hk (d : Fin (c + 1)) : w.length = d.val ↔ d = k := by
        constructor
        · intro h; exact Fin.ext h.symm
        · intro h; subst d; rfl
      simp_rw [hk]
      simp
    · have hne (d : Fin (c + 1)) : w.length ≠ d.val := by omega
      simp only [hne, ite_false, Finset.sum_const_zero, hX w (Nat.lt_of_not_ge hw), smul_zero]

end PolycyclicRecognition

end

end OAI
