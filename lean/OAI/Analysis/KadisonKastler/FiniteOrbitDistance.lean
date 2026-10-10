import OAI.Analysis.KadisonKastler.WOTCoefficientDuality
import OAI.Analysis.KadisonKastler.WOTDistanceSeparation
import OAI.Analysis.FactorGeneration.Bicommutant

namespace OAI

/-! # Operator distance from finite simultaneous orbit estimates

Finite coefficient factorization turns orbit-projection bounds into dual
bounds. Weak operator separation then supplies norm approximants.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_orbit_dual_bound (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (horbit : ∀ (n : ℕ) (x : FiniteHilbert (Fin n) H),
      ‖diagonalOperator T x - (tupleOrbitClosure S x).starProjection (diagonalOperator T x)‖ ≤
        c * ‖x‖)
    (f : (H →WOT[ℂ] H) →L[ℂ] ℂ)
    (hf : ∀ a ∈ S, f (ContinuousLinearMapWOT.ofCLM a) = 0) :
    ‖f (ContinuousLinearMapWOT.ofCLM T)‖ ≤
      c * ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ := by
  obtain ⟨n, x, y, heq, hx, hy⟩ := wot_functional_sharp_coefficients f
  let ξ : FiniteHilbert (Fin n) H := WithLp.toLp 2 x
  let η : FiniteHilbert (Fin n) H := WithLp.toLp 2 y
  have heval (a : H →L[ℂ] H) : f (ContinuousLinearMapWOT.ofCLM a) =
      inner ℂ η (diagonalOperator a ξ) := by
    have hh := congrArg (fun g : (H →L[ℂ] H) →L[ℂ] ℂ => g a) heq
    change f (ContinuousLinearMapWOT.ofCLM a) = finiteOperatorCoefficient x y a at hh
    simpa only [finiteOperatorCoefficient_apply,
      PiLp.inner_apply, diagonalOperator_apply, ξ, η] using hh
  have hker : tupleOrbitClosure S ξ ≤ (innerSL ℂ η).toLinearMap.ker := by
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨a, rfl⟩
      change inner ℂ η (diagonalOperator a.val ξ) = 0
      rw [← heval, hf a.val a.property]
    · exact (innerSL ℂ η).isClosed_ker
  have horth : inner ℂ η ((tupleOrbitClosure S ξ).starProjection
      (diagonalOperator T ξ)) = 0 :=
    hker ((tupleOrbitClosure S ξ).starProjection_apply_mem _)
  have hξ : ‖ξ‖ ^ 2 ≤ ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ := by
    simpa only [PiLp.norm_sq_eq_of_L2, ξ] using hx
  have hη : ‖η‖ ^ 2 ≤ ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ := by
    simpa only [PiLp.norm_sq_eq_of_L2, η] using hy
  have hprod : ‖η‖ * ‖ξ‖ ≤ ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ := by
    nlinarith [sq_nonneg (‖η‖ - ‖ξ‖)]
  rw [heval]
  calc
    ‖inner ℂ η (diagonalOperator T ξ)‖ =
        ‖inner ℂ η (diagonalOperator T ξ -
          (tupleOrbitClosure S ξ).starProjection (diagonalOperator T ξ))‖ := by
      rw [inner_sub_right, horth, sub_zero]
    _ ≤ ‖η‖ * ‖diagonalOperator T ξ -
        (tupleOrbitClosure S ξ).starProjection (diagonalOperator T ξ)‖ := norm_inner_le_norm _ _
    _ ≤ ‖η‖ * (c * ‖ξ‖) := mul_le_mul_of_nonneg_left (horbit n ξ) (norm_nonneg _)
    _ = c * (‖η‖ * ‖ξ‖) := by ring
    _ ≤ c * ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ :=
      mul_le_mul_of_nonneg_left hprod hc

theorem exists_near_algebra_of_finite_orbit_bound
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S)
    (T : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (horbit : ∀ (n : ℕ) (x : FiniteHilbert (Fin n) H),
      ‖diagonalOperator T x - (tupleOrbitClosure S x).starProjection (diagonalOperator T x)‖ ≤
        c * ‖x‖)
    {r : ℝ} (hr : c < r) : ∃ D ∈ S, ‖D - T‖ < r :=
  exists_near_subspace_of_wot_dual_bound S.toSubmodule hS T hc
    (fun f hf => finite_orbit_dual_bound S T hc horbit f hf) hr

end

end KadisonKastler

end OAI
