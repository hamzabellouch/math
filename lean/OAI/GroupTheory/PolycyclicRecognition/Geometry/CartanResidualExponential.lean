import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanResidualDerivation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanResidualAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRootWidths

namespace OAI

/-! # Polynomial formulas for the residual Cartan automorphism

The global residual Lie automorphism agrees with the analytic exponential of
the nilpotent residual operator on every root. This connects its algebraic
construction to the root-space estimates.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- The residual automorphism is an explicit finite real Lie polynomial. -/
theorem cartanIdealResidualAutomorphism_apply (h : H) (x : cartanRootIdeal H) :
    cartanIdealResidualAutomorphism T H h x =
      ∑ k ∈ Finset.range (finrank ℝ L), ((k.factorial : ℝ)⁻¹) •
        ((cartanIdealResidualDerivation T H h).toLinearMap ^ k) x := by
  let : Module ℚ (cartanRootIdeal H) := Module.compHom _ (algebraMap ℚ ℝ)
  change IsNilpotent.exp (cartanIdealResidualDerivation T H h).toLinearMap x = _
  rw [IsNilpotent.exp_eq_sum (cartanIdealResidualDerivation_pow_eq_zero T H h)]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Rat.cast_smul_eq_qsmul ℝ]
  simp only [Rat.cast_inv, Rat.cast_natCast]

/-- Every residual power preserves its actual generalized root space. -/
theorem cartanIdealResidualDerivation_pow_root_mem (h : H) (χ : Weight ℝ H L)
    (k : ℕ) (x : cartanRootIdeal H) (hx : (x : L) ∈ rootSpace H χ) :
    (((cartanIdealResidualDerivation T H h).toLinearMap ^ k) x : L) ∈ rootSpace H χ := by
  rw [cartanIdealResidualDerivation_pow_coe]
  induction k generalizing x with
  | zero => exact hx
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    exact ih (cartanIdealResidualDerivation T H h x)
      (cartanResidualDerivation_root_mem T H h χ hx)

/-- The finite exponential preserves each root space. -/
theorem cartanIdealResidualAutomorphism_root_mem (h : H) (χ : Weight ℝ H L)
    (x : cartanRootIdeal H) (hx : (x : L) ∈ rootSpace H χ) :
    (cartanIdealResidualAutomorphism T H h x : L) ∈ rootSpace H χ := by
  rw [cartanIdealResidualAutomorphism_apply]
  change (cartanRootIdeal H).incl (∑ k ∈ Finset.range (finrank ℝ L),
    ((k.factorial : ℝ)⁻¹) • ((cartanIdealResidualDerivation T H h).toLinearMap ^ k) x) ∈ _
  rw [map_sum]
  simp only [map_smul]
  apply (rootSpace H χ).sum_mem
  intro k _
  exact (rootSpace H χ).smul_mem _
    (cartanIdealResidualDerivation_pow_root_mem T H h χ k x hx)

end PolycyclicRecognition

end

end OAI
