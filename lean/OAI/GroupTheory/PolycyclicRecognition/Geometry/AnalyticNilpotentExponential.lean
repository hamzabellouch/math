import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.RingTheory.Nilpotent.Exp

namespace OAI

/-! # Agreement of analytic and finite nilpotent exponentials -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]

theorem analytic_exp_eq_nilpotent_exp {a : A} (ha : IsNilpotent a) :
    NormedSpace.exp a = IsNilpotent.exp a := by
  obtain ⟨n, hn⟩ := ha
  rw [IsNilpotent.exp_eq_sum hn, NormedSpace.exp_eq_tsum ℚ]
  apply tsum_eq_sum
  intro k hk
  have hnk : n ≤ k := by simpa using hk
  rw [pow_eq_zero_of_le hnk hn, smul_zero]

theorem isNilpotent_analytic_exp_sub_one {a : A} (ha : IsNilpotent a) :
    IsNilpotent (NormedSpace.exp a - 1) := by
  rw [analytic_exp_eq_nilpotent_exp ha]
  exact ha.isNilpotent_exp_sub_one

end PolycyclicRecognition

end

end OAI
