import OAI.Analysis.Mahler.DCForms
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes

 theorem contDiffAt_of_toMultilinear {d n : ℕ} {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ} {x : X}
    (hf : ContDiffAt ℝ 1 (fun y => (f y).toContinuousMultilinearMap) x) :
    ContDiffAt ℝ 1 f x := by
  let J : ((Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ) →L[ℝ] ((Fin d → ℝ) [×n]→L[ℝ] ℝ) :=
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
  have hJ : LinearMap.ker J.toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.mpr ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  obtain ⟨Q, hQ⟩ := J.toLinearMap.exists_leftInverse_of_injective hJ
  let : FiniteDimensional ℝ ((Fin d → ℝ) [×n]→L[ℝ] ℝ) :=
    FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear)
      ContinuousMultilinearMap.toMultilinearMap_injective
  let Qc := Q.toContinuousLinearMap
  have he : (fun y => Qc ((f y).toContinuousMultilinearMap)) = f := by
    funext y
    exact congrArg (fun L => L (f y)) hQ
  rw [← he]
  exact Qc.contDiff.contDiffAt.comp x hf

/-- The pullback operation is C1 jointly in the form and the linear map.
It is polynomial in the linear map, so C1 regularity needs no extra premise. -/
theorem contDiffAt_compAlternating {d n : ℕ} {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ}
    {L : X → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {x : X}
    (hf : ContDiffAt ℝ 1 f x) (hL : ContDiffAt ℝ 1 L x) :
    ContDiffAt ℝ 1 (fun y => (f y).compContinuousLinearMap (L y)) x := by
  apply contDiffAt_of_toMultilinear
  let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin n => Fin d → ℝ) (fun _ : Fin n => Fin d → ℝ) ℝ
  have hC : ContDiffAt ℝ 1 (fun y => C (fun _ => L y)) x := by
    exact (ContinuousMultilinearMap.contDiffAt
      (F := ((Fin d → ℝ) [×n]→L[ℝ] ℝ) →L[ℝ] ((Fin d → ℝ) [×n]→L[ℝ] ℝ)) C).comp x
        (contDiffAt_pi.mpr (fun _ : Fin n => hL))
  let J : ((Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ) →L[ℝ] ((Fin d → ℝ) [×n]→L[ℝ] ℝ) :=
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
  have hF : ContDiffAt ℝ 1 (fun y => (f y).toContinuousMultilinearMap) x :=
    J.contDiff.contDiffAt.comp x hf
  exact hC.clm_apply hF

/-- A C2 parametrization and C1 ambient form give a C1 actual pullback. -/
theorem contDiffAt_pullbackForm {d n : ℕ}
    {φ : (Fin d → ℝ) → (Fin d → ℝ)}
    {ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ} {x : Fin d → ℝ}
    (hφ : ContDiffAt ℝ 2 φ x) (hω : ContDiffAt ℝ 1 ω (φ x)) :
    ContDiffAt ℝ 1 (pullbackForm φ ω) x := by
  exact contDiffAt_compAlternating (hω.comp x (hφ.of_le (by simp)))
    (hφ.fderiv_right (by norm_num))

end MahlerStokes

end

end OAI
