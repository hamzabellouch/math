import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedSolverScale
import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedSolverFacts

namespace OAI

/-! Monotonicity of the input seminorm at smaller unperturbed scales. -/
noncomputable section
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open WeightedEstimates PhaseMean

variable {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : TopologicalSpace.Compacts Base}

lemma norm_atUnperturbedScale_le (c : PolynomialSolveData P 0 G hG φ K 1 1)
    (τ : ℝ) (s : ℝ≥0) (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (f : SupportedField (F := ComplexTensor) (modeSupport K)) (m : ℕ) :
    (c.atUnperturbedScale τ s hs1).norm f m ≤ c.norm f m := by
  change supportedWeightedSeminorm _ s m _ ≤ supportedWeightedSeminorm _ 1 m _
  apply supportedSeminorm_le_of_weightedBound hs (apply_nonneg _ _)
  exact (weightedBound_of_supportedSeminorm 1 m _).shrink_scale s.coe_nonneg hs1

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
