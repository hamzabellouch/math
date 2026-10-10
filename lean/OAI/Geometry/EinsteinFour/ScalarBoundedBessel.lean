import OAI.Geometry.EinsteinFour.ScalarContinuousLift
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Complex.OperatorNorm

namespace OAI

/-! Finite Bessel bounds for bounded continuous local heat coefficients. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι : Type*} {v : ι → E}

theorem scalarFunctional_bessel (hv : Orthonormal ℝ v) (L : E →L[ℝ] ℝ) (s : Finset ι) :
    ∑ i ∈ s, (L (v i)) ^ 2 ≤ ‖L‖ ^ 2 := by
  have h := hv.sum_inner_products_le (s := s) ((InnerProductSpace.toDual ℝ E).symm L)
  have he (i : ι) : inner ℝ (v i) ((InnerProductSpace.toDual ℝ E).symm L) = L (v i) := by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  simp_rw [he, Real.norm_eq_abs, sq_abs] at h
  exact h.trans_eq (congrArg (fun x : ℝ => x ^ 2) ((InnerProductSpace.toDual ℝ E).symm.norm_map L))

theorem scalarComplexFunctional_bessel (hv : Orthonormal ℝ v) (L : E →L[ℝ] ℂ)
    (s : Finset ι) : ∑ i ∈ s, ‖L (v i)‖ ^ 2 ≤ 2 * ‖L‖ ^ 2 := by
  have hr := scalarFunctional_bessel hv (Complex.reCLM.comp L) s
  have hi := scalarFunctional_bessel hv (Complex.imCLM.comp L) s
  have hR : ‖Complex.reCLM.comp L‖ ≤ ‖L‖ := by
    simpa only [Complex.reCLM_norm, one_mul] using Complex.reCLM.opNorm_comp_le L
  have hI : ‖Complex.imCLM.comp L‖ ≤ ‖L‖ := by
    simpa only [Complex.imCLM_norm, one_mul] using Complex.imCLM.opNorm_comp_le L
  have hsum : (∑ i ∈ s, ‖L (v i)‖ ^ 2) =
      (∑ i ∈ s, ((Complex.reCLM.comp L) (v i)) ^ 2) +
      ∑ i ∈ s, ((Complex.imCLM.comp L) (v i)) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Complex.normSq_apply, ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
      Complex.imCLM_apply, pow_two] using Complex.sq_norm (L (v i))
  rw [hsum]
  have hr' := pow_le_pow_left₀ (norm_nonneg _) hR 2
  have hi' := pow_le_pow_left₀ (norm_nonneg _) hI 2
  linarith

theorem scalarBoundedOperator_bessel {X : Type*} [TopologicalSpace X]
    (hv : Orthonormal ℝ v) (A : E →L[ℝ] (X →ᵇ ℂ)) (s : Finset ι) (x : X) :
    ∑ i ∈ s, ‖A (v i) x‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 := by
  let L : E →L[ℝ] ℂ := (BoundedContinuousFunction.evalCLM ℝ x).comp A
  have hb : ‖L‖ ≤ ‖A‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    exact (BoundedContinuousFunction.norm_coe_le_norm (A u) x).trans (A.le_opNorm u)
  have h := scalarComplexFunctional_bessel hv L s
  exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (by norm_num))

end
end PositiveEinsteinFour.Geometry

end OAI
