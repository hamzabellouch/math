import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace OAI

/-! # Projected coordinates for products of exponentials -/

noncomputable section
namespace PolycyclicRecognition
open scoped ContDiff

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem contDiff_algebra_exp : ContDiff ℝ ω (NormedSpace.exp : A → A) :=
  contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt

theorem exponential_product_derivative (K D : E →L[ℝ] A) :
    HasFDerivAt (fun x => NormedSpace.exp (K x) * NormedSpace.exp (D x)) (K + D) 0 := by
  have hK : HasFDerivAt (fun x => NormedSpace.exp (K x)) K 0 := by
    have h : HasFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (K 0) := by
      simpa only [map_zero] using (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A))
    simpa only [Function.comp_def, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
      using h.comp 0 K.hasFDerivAt
  have hD : HasFDerivAt (fun x => NormedSpace.exp (D x)) D 0 := by
    have h : HasFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (D 0) := by
      simpa only [map_zero] using (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A))
    simpa only [Function.comp_def, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
      using h.comp 0 D.hasFDerivAt
  convert hK.mul' hD using 1; simp [add_comm]

theorem exists_projected_exponential_coordinates [FiniteDimensional ℝ A]
    (K D : E →L[ℝ] A) (hinj : Function.Injective (K + D)) :
    ∃ P : A →L[ℝ] E,
      HasFDerivAt (fun x => P (NormedSpace.exp (K x) * NormedSpace.exp (D x) - 1))
        (ContinuousLinearMap.id ℝ E) 0 := by
  obtain ⟨p,hp⟩ := (K + D).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let P : A →L[ℝ] E := p.toContinuousLinearMap
  refine ⟨P, ?_⟩
  have h := P.hasFDerivAt.comp 0 ((exponential_product_derivative K D).sub_const 1)
  have he : P.comp (K + D) = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro x
    exact LinearMap.congr_fun hp x
  exact he ▸ h

end PolycyclicRecognition

end

end OAI
