import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMatrixFunctions
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BasisPolynomialMaps
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticNilpotentLogarithm

namespace OAI

/-! # Polynomial exponential charts from a faithful finite matrix model

Linear readout of the represented group gives polynomiality of the exponential.
A linear left inverse of the differential, applied to the finite matrix
logarithm, gives polynomiality of the inverse chart.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {d e m : ℕ} (b : Module.Basis (Fin d) ℝ V) (c : Module.Basis (Fin e) ℝ W)

theorem polynomial_chart_of_finite_matrix_exp
    (C : V ≃ W) (ρ : W → Matrix (Fin m) (Fin m) ℝ)
    (j : V →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ) (hj : Function.Injective j)
    (R : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] W)
    (hR : ∀ y, R (ρ y) = y)
    (hexp : ∀ x, ρ (C x) = NormedSpace.exp (j x))
    (hρ : HasPolynomialMatrixEntries (fun x => ρ (c.equivFun.symm x)))
    (k : ℕ) (hk : ∀ x, j x ^ (k + 1) = 0) :
    IsPolynomialInBasis b c C ∧ IsPolynomialInBasis c b C.symm := by
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hforward := ((HasPolynomialMatrixEntries.linear b j).exp_of_pow_eq_zero
    (k + 1) (fun x => hk (b.equivFun.symm x))).linear_image c R
  have hC (x : V) : R (NormedSpace.exp (j x)) = C x := by rw [← hexp, hR]
  have hp : IsPolynomialInBasis b c C := by
    simpa only [IsPolynomialInBasis, hC] using hforward
  obtain ⟨r, hr⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  have hinverse (y : W) : r (finiteNilpotentLog (k + 1) (ρ y - 1)) = C.symm y := by
    have he := hexp (C.symm y)
    rw [C.apply_symm_apply] at he
    rw [he]
    have hlog := finiteNilpotentLog_analytic_exp (j (C.symm y)) k (hk (C.symm y))
    exact (congrArg (fun A : Matrix (Fin m) (Fin m) ℝ => r A) hlog).trans
      (LinearMap.congr_fun hr _)
  have hback := ((hρ.sub (HasPolynomialMatrixEntries.const 1)).finiteLog (k + 1)).linear_image b r
  refine ⟨hp, ?_⟩
  simpa only [IsPolynomialInBasis, hinverse] using hback

end PolycyclicRecognition

end

end OAI
