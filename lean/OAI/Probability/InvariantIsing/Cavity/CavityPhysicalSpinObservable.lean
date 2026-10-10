import OAI.Probability.InvariantIsing.Cavity.CavitySpinObservable
import OAI.Probability.InvariantIsing.Cavity.CavityRotationArray

namespace OAI

/-! Summing the physical spectral components recovers the ordinary spin
overlap. Thus the scalar test needed by self-consistency has no frame dependence. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma sum_projectedOverlap_groups {N m : ℕ} (g : Fin N → Fin m)
    (U : Rotation N) (σ τ : Spin N) :
    (∑ a, projectedOverlap U (cavitySpectralGroup g a) σ τ) =
      (N : ℝ)⁻¹ * ∑ i, spinValue (σ i) * spinValue (τ i) := by
  calc
    _ = (N : ℝ)⁻¹ * ∑ a, ∑ i, if g i = a then
        U (spinVector σ) i * U (spinVector τ) i else 0 := by
      simp only [projectedOverlap,cavitySpectralGroup,Finset.sum_filter,Finset.mul_sum]
    _ = (N : ℝ)⁻¹ * ∑ i, U (spinVector σ) i * U (spinVector τ) i := by
      congr 1
      rw [Finset.sum_comm]
      simp
    _ = projectedOverlap U Finset.univ σ τ := by simp only [projectedOverlap]
    _ = _ := projectedOverlap_univ U σ τ

lemma cavity_physical_spin_observable {N m depth k : ℕ}
    (g : Fin N → Fin m)
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (j : Fin k)
    (σ : Fin 2 → (Spin N × LabeledLeaf depth) × Spin k) :
    cavityProjectedSpinTest
      (cavitySampledGroupBlock (cavityRotationEntry (cavitySpectralGroup g)) p)
      (cavitySpinObservable Φ hΦ j) σ =
      Φ ((N : ℝ)⁻¹ * ∑ i, spinValue ((σ 0).1.1 i) * spinValue ((σ 1).1.1 i)) *
        (spinValue ((σ 0).2 j) * spinValue ((σ 1).2 j)) := by
  simp only [cavityProjectedSpinTest,cavitySpinObservable,BoundedContinuousFunction.mkOfCompact_apply,
    ContinuousMap.coe_mk,cavitySampledGroupBlock,cavityRotationEntry,spectralJointEntry_spectral]
  rw [sum_projectedOverlap_groups]

end InvariantIsing

end

end OAI
