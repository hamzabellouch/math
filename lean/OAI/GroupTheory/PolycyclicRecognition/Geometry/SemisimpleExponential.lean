import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleSpectralOperator
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace OAI

/-! # Exponentiating scalar operators on eigenspaces -/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem continuousLinear_exp_eigenvector (T : V →L[ℂ] V) {x : V} {μ : ℂ}
    (hx : T x = μ • x) : NormedSpace.exp T x = Complex.exp μ • x := by
  have hp (n : ℕ) : (T ^ n) x = μ ^ n • x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hx,
        smul_smul, pow_succ, mul_comm]
  have h := (ContinuousLinearMap.apply ℂ V x).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) T)
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ).smul_const x
  rw [← Complex.exp_eq_exp_ℂ] at hs
  apply h.unique
  convert hs using 1
  ext n
  simp only [ContinuousLinearMap.apply_apply, smul_apply,
    hp, smul_smul, smul_eq_mul]

variable [FiniteDimensional ℂ V]

theorem exp_semisimpleSpectralOperator (S : Module.End ℂ V) (hS : S.IsSemisimple)
    (f : ℂ → ℂ) :
    (NormedSpace.exp (LinearMap.toContinuousLinearMap
      (semisimpleSpectralOperator S hS f))).toLinearMap =
      semisimpleSpectralOperator S hS (fun μ => Complex.exp (f μ)) := by
  apply semisimple_eigenspace_ext S hS
  intro μ x hx
  exact (continuousLinear_exp_eigenvector _
    (semisimpleSpectralOperator_apply S hS f hx)).trans
      (semisimpleSpectralOperator_apply S hS (fun μ => Complex.exp (f μ)) hx).symm

end PolycyclicRecognition

end

end OAI
