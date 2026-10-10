import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealSemisimpleLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.InvertibleJordanDecomposition
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CanonicalNilpotentLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticNilpotentExponential
import Mathlib.Algebra.Polynomial.Smeval

namespace OAI

/-! # Every squared real linear automorphism has a real logarithm

The semisimple factor uses the conjugation-compatible scalar logarithm of a
square. The unipotent factor uses its finite polynomial logarithm.
-/

noncomputable section
namespace PolycyclicRecognition

theorem commute_nilpotentLog_right {A : Type*} [Ring A] [Algebra ℚ A]
    {a b : A} (h : Commute a b) : Commute a (nilpotentLog b) := by
  unfold nilpotentLog finiteNilpotentLog
  rw [Polynomial.aeval_eq_smeval]
  exact (Polynomial.smeval_commute_left ℚ _ h.symm).symm

theorem analytic_exp_nilpotentLog {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
    (a : A) (ha : IsNilpotent a) : NormedSpace.exp (nilpotentLog a) = 1 + a := by
  rw [analytic_exp_eq_nilpotent_exp (nilpotentLog_nilpotent a ha), exp_nilpotentLog a ha]

theorem real_linear_square_has_log {n : ℕ} (A : Module.End ℝ (Fin n → ℝ))
    (hA : IsUnit A) :
    ∃ D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ),
      NormedSpace.exp D = LinearMap.toContinuousLinearMap (A ^ 2) := by
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) (Fin n → ℝ)
  let := NormedAlgebra.restrictScalars ℚ ℝ ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
  obtain ⟨S, U, hS, hU, hSU, hAeq, _⟩ := invertible_jordan_decomposition A hA
  let B := realSemisimpleSquareLog (S : Module.End ℝ (Fin n → ℝ)) hS
  let C := nilpotentLog (U - 1)
  have hBU : Commute B U := realSemisimpleSquareLog_commute _ hS U hSU
  have hBC : Commute B C := commute_nilpotentLog_right
    (hBU.sub_right (Commute.one_right _))
  have hEB : NormedSpace.exp (E B) = E ((S : Module.End ℝ (Fin n → ℝ)) ^ 2) := by
    apply ContinuousLinearMap.ext
    intro x
    exact DFunLike.congr_fun (exp_realSemisimpleSquareLog _ hS S.isUnit) x
  have hEC : NormedSpace.exp (E C) = E U := by
    have he : E C = nilpotentLog (E (U - 1)) :=
      (nilpotentLog_map E.toRingHom (U - 1) hU).symm
    have hn : IsNilpotent (E (U - 1)) := hU.map E.toRingHom
    rw [he, analytic_exp_nilpotentLog _ hn, map_sub, map_one]
    abel
  have hc : Commute (E B) (E C) := hBC.map E.toRingHom
  refine ⟨E B + (2 : ℕ) • E C, ?_⟩
  rw [NormedSpace.exp_add_of_commute (hc.smul_right (2 : ℕ)),
    NormedSpace.exp_nsmul, hEB, hEC, ← map_pow, ← map_mul, ← hSU.mul_pow,
    ← hAeq]
  rfl

end PolycyclicRecognition

end

end OAI
