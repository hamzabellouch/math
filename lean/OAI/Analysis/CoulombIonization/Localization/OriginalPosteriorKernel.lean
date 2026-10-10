import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ConditionalSandwich

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation ProbabilityTheory

def OriginalDatum (N K : ℕ) (_ell : Fin K → ℝ) (_j : ℕ) :=
  Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)

instance {N K : ℕ} {ell : Fin K → ℝ} {j : ℕ} :
    MeasurableSpace (OriginalDatum N K ell j) := observationInformation ell j

def originalDatum {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → OriginalDatum N K ell j := id

lemma originalDatum_measurable {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    Measurable (originalDatum (N := N) ell j) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap id (observationInformation ell j) ≤ _
  simpa only [MeasurableSpace.comap_id] using (observationInformation_le (N := N) ell j)

lemma originalDatum_comap {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    MeasurableSpace.comap (originalDatum (N := N) ell j) inferInstance =
      observationInformation ell j := MeasurableSpace.comap_id

def originalRawKernel {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) : Kernel (OriginalDatum N K ell j) (Configuration N) :=
  condDistrib Prod.fst (originalDatum ell j) (physicalObservationLaw μ K)

instance originalRawKernel_markov {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) :
    IsMarkovKernel (originalRawKernel μ ell j) := by
  unfold originalRawKernel
  infer_instance

def kernelPosteriorTest {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (g : Space → ℝ) (z : OriginalDatum N K ell j) : ℝ :=
  ∫ x, ∑ i, g (x i) ∂originalRawKernel μ ell j z

lemma kernelPosteriorTest_measurable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g) :
    Measurable (kernelPosteriorTest μ ell j g) := by
  have h : StronglyMeasurable (fun p : OriginalDatum N K ell j × Configuration N =>
      ∑ i, g (p.2 i)) :=
    (Finset.measurable_sum _ (fun i _ => hg.comp ((measurable_pi_apply i).comp measurable_snd))).stronglyMeasurable
  exact h.integral_kernel_prod_right'.measurable

lemma kernelPosteriorTest_eq {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
      ∑ i, g (z.1 i)) (physicalObservationLaw μ K)) :
    posteriorTestValue μ ell j g =ᵐ[physicalObservationLaw μ K]
      fun z => kernelPosteriorTest μ ell j g (originalDatum ell j z) := by
  have h := condExp_ae_eq_integral_condDistrib (originalDatum_measurable (N := N) ell j)
    measurable_fst.aemeasurable
    ((Finset.measurable_sum _ (fun i _ => hg.comp (measurable_pi_apply i))).stronglyMeasurable) hi
  simpa only [originalDatum_comap,posteriorTestValue,kernelPosteriorTest,originalRawKernel,Function.comp_def] using h

lemma kernelPosteriorTest_tower {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) {j k : ℕ} (hjk : j ≤ k)
    {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
      ∑ i, g (z.1 i)) (physicalObservationLaw μ K)) :
    (physicalObservationLaw μ K)[(fun z => kernelPosteriorTest μ ell j g (originalDatum ell j z)) |
      observationInformation ell k] =ᵐ[physicalObservationLaw μ K]
      fun z => kernelPosteriorTest μ ell k g (originalDatum ell k z) := by
  exact (condExp_congr_ae (kernelPosteriorTest_eq μ ell j hg hi).symm).trans
    ((posteriorTestValue_tower μ ell hjk g).trans (kernelPosteriorTest_eq μ ell k hg hi))

end CoulombAtom

end

end OAI
