import OAI.Analysis.FiniteFactor.FiniteProductMixture
import OAI.Analysis.FiniteFactor.BiasedPairs.ReferenceDomination

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory CouplingParameters Finset
open scoped ENNReal
noncomputable section

def sourceResamplingKernel (I : Finset SourceCoordinate) :
    Kernel (SourceCoordinate → ℝ) (SourceCoordinate → ℝ) := by
  letI : ∀ i : SourceCoordinate, IsMarkovKernel
      (if i ∈ I then Kernel.const ℝ unitIntervalMeasure else Kernel.id) :=
    fun i => by split_ifs <;> infer_instance
  exact independentKernel (fun i : SourceCoordinate =>
    if i ∈ I then Kernel.const ℝ unitIntervalMeasure else Kernel.id)

instance sourceResamplingKernel_markov (I : Finset SourceCoordinate) :
    IsMarkovKernel (sourceResamplingKernel I) := by
  unfold sourceResamplingKernel
  infer_instance

theorem sourceResamplingKernel_apply (I : Finset SourceCoordinate) (x : SourceCoordinate → ℝ) :
    sourceResamplingKernel I x = finiteChoiceLaw (fun i => Measure.dirac (x i))
      (fun _ => unitIntervalMeasure) I := by
  dsimp [sourceResamplingKernel,independentKernel,finiteChoiceLaw]
  congr 1
  funext i
  by_cases hi : i ∈ I <;> simp [hi]; rfl

theorem sourceFiniteReferenceKernel_apply (F : Finset SourceCoordinate) (x : SourceCoordinate → ℝ) :
    sourceFiniteReferenceKernel F x = finiteAverageLaw (fun i => Measure.dirac (x i))
      (fun _ => unitIntervalMeasure) F := by
  dsimp [sourceFiniteReferenceKernel,independentKernel,finiteAverageLaw]
  congr 1
  funext i
  by_cases hi : i ∈ F
  · simp only [ite_eq_left hi]
    rfl
  · simp only [ite_eq_right hi]
    rfl

/-- The exact finite replacement-pattern expansion of the reference kernel. -/
theorem sourceFiniteReferenceKernel_mixture (F : Finset SourceCoordinate) (x : SourceCoordinate → ℝ) :
    sourceFiniteReferenceKernel F x = ((2 : ℝ≥0∞)⁻¹)^F.card •
      ∑ I ∈ F.powerset, sourceResamplingKernel I x := by
  rw [sourceFiniteReferenceKernel_apply,finiteAverageLaw_eq_sum]
  simp_rw [sourceResamplingKernel_apply]

/-- Integrating over the actual Haar base preserves the finite mixture formula. -/
theorem sourceFiniteReference_compProd_mixture (F : Finset SourceCoordinate) :
    sourceSamplingHaar ⊗ₘ sourceFiniteReferenceKernel F =
      ((2 : ℝ≥0∞)⁻¹)^F.card •
        ∑ I ∈ F.powerset, sourceSamplingHaar ⊗ₘ sourceResamplingKernel I := by
  apply Measure.ext
  intro S hS
  rw [Measure.compProd_apply hS,Measure.smul_apply,Measure.finsetSum_apply,smul_eq_mul]
  simp_rw [sourceFiniteReferenceKernel_mixture,Measure.smul_apply,Measure.finsetSum_apply,smul_eq_mul]
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun I _ =>
      Kernel.measurable_kernel_prodMk_left hS),
    lintegral_finsetSum F.powerset (fun I _ => Kernel.measurable_kernel_prodMk_left hS)]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  exact (Measure.compProd_apply hS).symm

end
end FiniteFactor

end OAI
