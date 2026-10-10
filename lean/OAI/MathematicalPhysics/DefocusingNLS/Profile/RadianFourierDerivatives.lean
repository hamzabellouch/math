import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSamplingSum
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

namespace OAI

/-! # Derivative symbols for the manuscript's radian Fourier transform -/

open scoped SchwartzMap FourierTransform RealInnerProductSpace Laplacian LineDeriv

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radianFourierKernel_lineDeriv (ψ : 𝓢(E, ℂ)) (v ξ : E) :
    radianFourierKernel (∂_{v} ψ) ξ =
      (inner ℝ ξ v : ℂ) * Complex.I * radianFourierKernel ψ ξ := by
  have hi : (fun x : E => inner ℝ x v).HasTemperateGrowth :=
    ((innerSL ℝ).flip v).hasTemperateGrowth
  change (𝓕 (∂_{v} ψ) : 𝓢(E, ℂ)) ((2 * Real.pi)⁻¹ • ξ) =
    (inner ℝ ξ v : ℂ) * Complex.I * (𝓕 ψ : 𝓢(E, ℂ)) ((2 * Real.pi)⁻¹ • ξ)
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hi,
    Complex.real_smul, real_inner_smul_left, smul_eq_mul]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem radianFourierKernel_laplacian (ψ : 𝓢(E, ℂ)) (ξ : E) :
    radianFourierKernel (Δ ψ) ξ = -((‖ξ‖ ^ 2 : ℝ) : ℂ) * radianFourierKernel ψ ξ := by
  rw [SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 12) ℝ)]
  change radianFourierCLM (∑ j : Fin 12,
    ∂_{(EuclideanSpace.basisFun (Fin 12) ℝ) j}
      (∂_{(EuclideanSpace.basisFun (Fin 12) ℝ) j} ψ)) ξ = _
  rw [map_sum]
  simp only [sum_apply]
  change (∑ j : Fin 12, radianFourierKernel
    (∂_{(EuclideanSpace.basisFun (Fin 12) ℝ) j}
      (∂_{(EuclideanSpace.basisFun (Fin 12) ℝ) j} ψ)) ξ) = _
  simp_rw [radianFourierKernel_lineDeriv]
  have hterm (j : Fin 12) :
      (inner ℝ ξ ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) * Complex.I *
        ((inner ℝ ξ ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) * Complex.I *
          radianFourierKernel ψ ξ) =
      -((inner ℝ ξ ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) ^ 2) *
        radianFourierKernel ψ ξ := by
    calc
      _ = (Complex.I ^ 2) * (inner ℝ ξ ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) ^ 2 *
          radianFourierKernel ψ ξ := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, Finset.sum_neg_distrib]
  have hs : (∑ j : Fin 12, (inner ℝ ξ ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) ^ 2) =
      ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast (EuclideanSpace.basisFun (Fin 12) ℝ).sum_sq_inner_left ξ
  rw [hs]

end DefocusingNLS

end OAI
