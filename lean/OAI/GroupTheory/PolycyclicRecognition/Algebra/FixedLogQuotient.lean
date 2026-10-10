import OAI.GroupTheory.PolycyclicRecognition.Algebra.FixedPowerLogarithms
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticDerivationFlow

namespace OAI

/-! # Fixed logarithms preserve a quotient with a fixed linear section -/

noncomputable section
namespace PolycyclicRecognition
variable {L V : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [AddCommGroup V] [Module ℝ V]

omit [FiniteDimensional ℝ L] in
theorem fixed_log_projection_zero (A : L ≃ₗ⁅ℝ⁆ L) (D : LieDerivation ℝ L L)
    (hcomm : ∀ T : Module.End ℝ L, Commute A.toLinearMap T → Commute D.toLinearMap T)
    (hfixed : ∀ x, A x = x → D x = 0)
    (p : Module.End ℝ L) (hap : ∀ x, A (p x) = p x) (hpa : ∀ x, p (A x) = p x) :
    p * D.toLinearMap = 0 := by
  have hc : Commute A.toLinearMap p := by
    apply LinearMap.ext
    intro x
    exact (hap x).trans (hpa x).symm
  have hdp : D.toLinearMap * p = 0 := by
    apply LinearMap.ext
    intro x
    exact hfixed (p x) (hap x)
  rw [← (hcomm p hc).eq, hdp]

theorem exp_preserves_projected_quotient (D p : Module.End ℝ L)
    (hpd : p * D = 0) (f : L →ₗ[ℝ] V) (hfp : ∀ x, f (p x) = f x) (x : L) :
    f (NormedSpace.exp (LinearMap.toContinuousLinearMap D) x) = f x := by
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) L
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  have hc : SemiconjBy (E p) (E D) 0 := by
    change E p * E D = 0 * E p
    rw [← map_mul, hpd, map_zero, zero_mul]
  have he : E p * NormedSpace.exp (E D) = E p := by
    have h := hc.exp_right
    simpa only [SemiconjBy, NormedSpace.exp_zero, one_mul] using h
  have hx : p (NormedSpace.exp (E D) x) = p x := DFunLike.congr_fun he x
  change f (NormedSpace.exp (E D) x) = f x
  exact (hfp _).symm.trans ((congrArg f hx).trans (hfp x))

theorem exp_fixes_projection (D p : Module.End ℝ L)
    (hdp : D * p = 0) (x : L) :
    NormedSpace.exp (LinearMap.toContinuousLinearMap D) (p x) = p x := by
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) L
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  have hc : SemiconjBy (E p) 0 (E D) := by
    change E p * 0 = E D * E p
    rw [← map_mul, hdp, map_zero, mul_zero]
  have he : NormedSpace.exp (E D) * E p = E p := by
    have h := hc.exp_right
    simpa only [SemiconjBy, NormedSpace.exp_zero, mul_one] using h.symm
  exact DFunLike.congr_fun he x

end PolycyclicRecognition

end

end OAI
