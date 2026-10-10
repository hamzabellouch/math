import Mathlib
import OAI.Analysis.CoulombIonization.Variational.MasterKernelFubini

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom

lemma original_configuration_integrable {N K : ℕ} (μ : Measure (Configuration N))
    (f : Configuration N → ℝ) (hf : Measurable f) (hi : Integrable f μ) :
    Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) => f z.1)
      (physicalObservationLaw μ K) := by
  apply (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).mp
  simpa [physicalObservationLaw,Measure.map_fst_prod] using hi

lemma kernelPosteriorTest_setIntegral {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun x : Configuration N => ∑ i, g (x i)) μ)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) :
    (∫ z in A, kernelPosteriorTest μ ell j g (originalDatum ell j z) ∂physicalObservationLaw μ K) =
      ∫ z in A, ∑ i, g (z.1 i) ∂physicalObservationLaw μ K := by
  rw [←integral_congr_ae (ae_restrict_of_ae (kernelPosteriorTest_eq_of_integrable μ ell j hg hi))]
  exact setIntegral_condExp (observationInformation_le ell j)
    (original_configuration_integrable μ _
      (Finset.measurable_sum _ (fun i _ => hg.comp (measurable_pi_apply i))) hi) hA

end CoulombAtom

end

end OAI
