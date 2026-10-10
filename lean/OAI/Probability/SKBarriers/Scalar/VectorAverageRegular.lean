import Mathlib
import OAI.Probability.SKBarriers.Replicas.VectorBranch

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Composition
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Norm G]
theorem HasExpGrowth.compCLM {f : F → G} (hf : HasExpGrowth f) (L : E →L[ℝ] F) :
    HasExpGrowth (f ∘ L) := by
  obtain ⟨C,M,hC,hM,h⟩ := hf
  refine ⟨C,M*‖L‖,hC,mul_nonneg hM (norm_nonneg _),fun x => (h (L x)).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.2
  have H := mul_le_mul_of_nonneg_left (L.le_opNorm x) hM
  simpa only [mul_assoc] using H
end Composition
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorStepAverage_expGrowth {f g : E → ℝ} (hf : BoundedDerivs f)
    (hg : HasExpGrowth g) (m : ℝ) (v : E) : HasExpGrowth (vectorStepAverage m v f g) :=
  gaussianAverage_expGrowth (hf.compCLM (vectorTranslation v)) m (hg.compCLM (vectorTranslation v))

theorem vectorStepAverage_continuous {f g : E → ℝ} (hf : BoundedDerivs f)
    (hg : HasExpGrowth g) (hc : Continuous g) (m : ℝ) (v : E) :
    Continuous (vectorStepAverage m v f g) :=
  gaussianAverage_continuous_of_expGrowth (hf.compCLM (vectorTranslation v)) m
    (hg.compCLM (vectorTranslation v)) (hc.comp (vectorTranslation v).continuous)

theorem vectorHierarchy_regular (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E)
    {f : E → ℝ} (hf : BoundedDerivs f) : BoundedDerivs (vectorHierarchy n m v f) := by
  induction n generalizing f with
  | zero => exact hf
  | succ n ih => exact ih _ _ (vectorStep_regular hf _ _)

theorem vectorHierarchyAverage_regular (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E)
    {f g : E → ℝ} (hf : BoundedDerivs f) (hg : HasExpGrowth g) (hc : Continuous g) :
    Continuous (vectorHierarchyAverage n m v f g) ∧ HasExpGrowth (vectorHierarchyAverage n m v f g) := by
  induction n generalizing f g with
  | zero => exact ⟨hc,hg⟩
  | succ n ih =>
    exact ih _ _ (vectorStep_regular hf _ _)
      (vectorStepAverage_expGrowth hf hg _ _) (vectorStepAverage_continuous hf hg hc _ _)

end Vector

end SK.Analytic

end
end

end OAI
