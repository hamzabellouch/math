import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSolveFactors
import OAI.Geometry.SurfaceImmersion.Correction.CoordinateLinearizedCalculus

namespace OAI

/-! The finite polynomial solver at parameter zero is exactly the metric
linearization; its explicit size and residual budgets are nonnegative. -/
noncomputable section
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean

lemma coordinateFullLinearized_unperturbed {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (G : Base → Space) (X : RealModes.RField 4) :
    coordinateFullLinearized P 0 G X =
      RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X := by
  funext x k
  simp [coordinateFullLinearized,coordinateRealLinearized,linearized]

namespace PolynomialSolveData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : TopologicalSpace.Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

lemma size_nonneg (f : SupportedField (F := ComplexTensor) (modeSupport K)) (q m : ℕ) :
    0 ≤ c.size f q m := by
  rw [c.size_eq_factor]
  exact mul_nonneg (c.sizeFactor_nonneg q m) (apply_nonneg _ _)

lemma residual_nonneg (hη : 0 ≤ τ/s + ε/τ^tensorLoss P)
    (f : SupportedField (F := ComplexTensor) (modeSupport K)) (q m : ℕ) :
    0 ≤ c.residual f q m := by
  rw [c.residual_eq_factor]
  exact mul_nonneg (mul_nonneg (pow_nonneg hη _) (c.residualFactor_nonneg q m)) (apply_nonneg _ _)

end PolynomialSolveData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
