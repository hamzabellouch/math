import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteExponentialLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticNilpotentExponential

namespace OAI

/-! # Finite logarithms of analytic unipotent exponentials -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]

theorem finiteNilpotentLog_analytic_exp (a : A) (n : ℕ) (ha : a ^ (n + 1) = 0) :
    finiteNilpotentLog (n + 1) (NormedSpace.exp a - 1) = a := by
  rw [analytic_exp_eq_nilpotent_exp ⟨n + 1, ha⟩]
  exact finiteNilpotentLog_exp a n ha

theorem analytic_exp_finiteNilpotentLog (a : A) (n : ℕ) (ha : a ^ (n + 1) = 0) :
    NormedSpace.exp (finiteNilpotentLog (n + 1) a) = 1 + a := by
  rw [analytic_exp_eq_nilpotent_exp ⟨n + 1, finiteNilpotentLog_pow a n ha⟩]
  exact exp_finiteNilpotentLog a n ha

end PolycyclicRecognition

end

end OAI
