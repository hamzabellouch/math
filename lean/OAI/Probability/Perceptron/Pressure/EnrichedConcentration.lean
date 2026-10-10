import Mathlib
import OAI.Probability.Perceptron.Variational.GaussianLinearVariance

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma enrichedTerminal_C1 (n M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (p : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (htop : ℝ) :
    ∃ D : EnrichedMark (n+1) (n+1) p → StrongDual ℝ (EnrichedMark (n+1) (n+1) p),
      Continuous D ∧ ∀ x, HasFDerivAt (enrichedTerminal n M f g p u htop) (D x) x := by
  let W := normalizedPatternEnergy (n+1) M f g
  let V := fun x : NormalizedSpin (n+1) => innerSL ℝ (sourceEnrichedFeature (n+1) p u x)
  have hW : Continuous W := (normalizedPatternEnergy_continuous (n+1) M f).comp
    (continuous_const.prodMk continuous_id)
  have hV : Continuous V := (innerSL ℝ).continuous.comp (enrichedFeature_continuous _ _ _ _ _)
  have hWB : ∀ x, |W x| ≤ (M:ℝ)*‖f‖ := normalizedPatternEnergy_bound _ _ _ _
  have hVB : ∀ x, ‖V x‖ ≤ enrichedFeatureBound (n+1) u := fun x => by
    change ‖innerSL ℝ (sourceEnrichedFeature (n+1) p u x)‖ ≤ _
    rw [innerSL_apply_norm,sourceEnrichedFeature_norm]
  refine ⟨vectorLogDerivative (unitSphereLaw (n+1)) W V,
    vectorLogDerivative_continuous (unitSphereLaw (n+1)) hW.measurable hV.measurable
      (enrichedFeatureBound (n+1) u).coe_nonneg hWB hVB,?_⟩
  intro x
  exact (vectorLogPartition_hasFDerivAt (unitSphereLaw (n+1)) hW.measurable hV.measurable
    (enrichedFeatureBound (n+1) u).coe_nonneg hWB hVB x).sub_const _

lemma enrichedCascadeLog_fixed_patterns_variance (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    MemLp (enrichedCascadeLog n M k f g p d u h) 2 (enrichedDisorderLaw n k p z) ∧
      variance (enrichedCascadeLog n M k f g p d u h) (enrichedDisorderLaw n k p z) ≤
        cascadeLogFluctuationConstant k z+(Real.pi^2/8)*
          ((enrichedFeatureBound (n+1) u:ℝ)*‖enrichedRootMap p d h‖)^2 := by
  obtain ⟨D,hD,hd⟩ := enrichedTerminal_C1 n M f g p u (h (Fin.last k))
  exact gaussianLinearCascadeLog_variance (enrichedIncrementMap p d h) (enrichedRootMap p d h)
    (enrichedTerminal_lipschitz n M f g p u _) hd hD k z hz hz0 hz1

end SphericalPerceptronFreeEnergy
end

end OAI
