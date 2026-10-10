import OAI.Analysis.KadisonKastler.ScalarGaugeWindowBalance
import OAI.Analysis.KadisonKastler.CoreTraceTomitaCoordinates

namespace OAI

/-! # The two square-root spectral weights in a cyclic gauge model -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

def cyclicLeftRootVector : ModularCyclicSpace M J Ω x :=
  ContinuousMap.toLp 2 (modularCyclicMeasure (M := M) J Ω x) ℂ
    (resolventSqrtFunction (graphResolvent M J Ω 1))

def cyclicRightRootVector : ModularCyclicSpace M J Ω x :=
  ContinuousMap.toLp 2 (modularCyclicMeasure (M := M) J Ω x) ℂ
    (resolventComplementSqrtFunction (graphResolvent M J Ω 1))

omit [TopologicalSpace.SeparableSpace H] in
include hsep hcyc in
theorem cyclicRootScalarBalance :
    let μ := modularCyclicMeasure (M := M) J Ω x
    let f := (Lp.fourierTransformₗᵢ ℝ ℂ).symm coreTraceFrequencyScalar
    ∀ᵐ s ∂μ,
      cyclicLeftRootVector (M := M) J Ω x s • regularFrequencyWindow 0 1
        ((star (regularCharacterUnitary (H := ℂ) (resolventLogFrequency s.val)) :
          RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) =
      cyclicRightRootVector (M := M) J Ω x s •
        (star (regularCharacterUnitary (H := ℂ) (resolventLogFrequency s.val)) :
          RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
        (regularFrequencyWindow 0 1
          ((regularCharacterUnitary (H := ℂ) (resolventLogFrequency s.val) :
            RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f)) := by
  let μ := modularCyclicMeasure (M := M) J Ω x
  filter_upwards [graphResolventVectorMeasure_interior J Ω hsep hcyc x,
    ContinuousMap.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℂ)
      (resolventSqrtFunction (graphResolvent M J Ω 1)),
    ContinuousMap.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℂ)
      (resolventComplementSqrtFunction (graphResolvent M J Ω 1))]
    with s hs hv hw
  change cyclicLeftRootVector (M := M) J Ω x s = _ at hv
  change cyclicRightRootVector (M := M) J Ω x s = _ at hw
  rw [hv, hw]
  exact coreTrace_scalarGauge_balance hs.1 hs.2

theorem cyclicSqrtGaugeBalance :
    let E := ModularCyclicSpace M J Ω x
    let G : unitary (RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E) :=
      modularCyclicGauge J Ω hsep hcyc x
    let f := (Lp.fourierTransformₗᵢ ℝ ℂ).symm coreTraceFrequencyScalar
    regularFrequencyWindow 0 1
      ((star G : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E)
        (scalarLpTensor volume f (cyclicLeftRootVector (M := M) J Ω x))) =
      (star G : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E)
        (regularFrequencyWindow 0 1
          ((G : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E)
            (scalarLpTensor volume f (cyclicRightRootVector (M := M) J Ω x)))) := by
  have h := scalarGaugeWindowBalance (modularCyclicMeasure (M := M) J Ω x)
    (fun s => resolventLogFrequency s.val)
    (resolventLogFrequency_measurable.comp measurable_subtype_coe)
    (modularCyclicGauge J Ω hsep hcyc x) (cyclicGauge_swap J Ω hsep hcyc x)
    ((Lp.fourierTransformₗᵢ ℝ ℂ).symm coreTraceFrequencyScalar)
    (cyclicLeftRootVector (M := M) J Ω x) (cyclicRightRootVector (M := M) J Ω x)
    (cyclicRootScalarBalance J Ω hsep hcyc x)
  exact h

end

end KadisonKastler

end OAI
