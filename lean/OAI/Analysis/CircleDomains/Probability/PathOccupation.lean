import OAI.Analysis.CircleDomains.Modulus.PathLengthKernel
import OAI.Analysis.CircleDomains.Probability.MomentLawBounds
import Mathlib.Probability.Kernel.MeasurableLIntegral

namespace OAI

/-! Physical occupation of a rectifiable metric path, and its mean under a law.
The measure records arclength with multiplicity, including repeated traversals. -/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def pathOccupation (γ : RectifiablePath X) : Measure X :=
  (pathLengthMeasure γ).map γ.val

instance (γ : RectifiablePath X) : IsFiniteMeasure (pathOccupation γ) := by
  unfold pathOccupation
  infer_instance

theorem pathOccupation_apply (γ : RectifiablePath X) {s : Set X} (hs : MeasurableSet s) :
    pathOccupation γ s = pathLengthMeasure γ (γ.val ⁻¹' s) :=
  Measure.map_apply γ.val.continuous.measurable hs

theorem pathOccupation_univ (γ : RectifiablePath X) :
    pathOccupation γ univ = eVariationOn γ.val univ := by
  rw [pathOccupation_apply γ MeasurableSet.univ, preimage_univ, pathLengthMeasure_univ]

theorem lintegral_pathOccupation (γ : RectifiablePath X) {g : X → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ x, g x ∂pathOccupation γ = ∫⁻ t, g (γ.val t) ∂pathLengthMeasure γ :=
  lintegral_map hg γ.val.continuous.measurable

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_pathOccupation : Measurable (pathOccupation (X := X)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have he : Measurable (fun p : RectifiablePath X × PathTime => p.1.val p.2) :=
    (continuous_eval.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).measurable
  have hm := Kernel.measurable_kernel_prodMk_left_of_finite
    (κ := pathLengthKernel (X := X)) (he hs) (fun γ => inferInstance)
  change Measurable (fun γ : RectifiablePath X =>
    pathLengthMeasure γ (γ.val ⁻¹' s)) at hm
  simpa only [pathOccupation_apply _ hs] using hm

def meanPathOccupation (μ : ProbabilityMeasure (RectifiablePath X)) : Measure X :=
  (μ : Measure (RectifiablePath X)).bind pathOccupation

theorem meanPathOccupation_apply (μ : ProbabilityMeasure (RectifiablePath X))
    {s : Set X} (hs : MeasurableSet s) :
    meanPathOccupation μ s = ∫⁻ γ, pathOccupation γ s ∂(μ : Measure _) :=
  Measure.bind_apply hs measurable_pathOccupation.aemeasurable

theorem lintegral_meanPathOccupation (μ : ProbabilityMeasure (RectifiablePath X))
    {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂meanPathOccupation μ =
      ∫⁻ γ, ∫⁻ t, g (γ.val t) ∂pathLengthMeasure γ ∂(μ : Measure _) := by
  rw [meanPathOccupation, Measure.lintegral_bind measurable_pathOccupation.aemeasurable
    hg.aemeasurable]
  apply lintegral_congr
  intro γ
  exact lintegral_pathOccupation γ hg

theorem measurable_meanPathOccupation : Measurable (meanPathOccupation (X := X)) :=
  (Measure.measurable_bind' measurable_pathOccupation).comp measurable_subtype_coe

theorem meanPathOccupation_mixture {Z : Type*} [MeasurableSpace Z]
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure (RectifiablePath X))
    (hlaw : Measurable law) :
    meanPathOccupation (probabilityMixture P law hlaw) =
      (P : Measure Z).bind (fun z => meanPathOccupation (law z)) := by
  apply Measure.ext
  intro s hs
  have hm : Measurable (fun z => meanPathOccupation (law z)) :=
    measurable_meanPathOccupation.comp hlaw
  rw [meanPathOccupation_apply _ hs, Measure.bind_apply hs hm.aemeasurable]
  simp_rw [meanPathOccupation_apply _ hs]
  exact lintegral_probabilityMixture P law hlaw
    ((Measure.measurable_coe hs).comp measurable_pathOccupation)

end CircleDomainRigidity

end

end OAI
