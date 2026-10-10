import OAI.Analysis.KadisonKastler.CyclicGaugeKernel
import OAI.Analysis.KadisonKastler.L2FourierNaturality
import OAI.Analysis.KadisonKastler.L2SwapIntertwining

namespace OAI

/-! # The full cyclic gauge under the L2 variable swap -/

namespace KadisonKastler

open MeasureTheory
open scoped TensorProduct

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

abbrev modularCyclicMeasure :=
  resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x

def modularCyclicGauge : unitary
    (RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
      RegularCoreHilbert (ModularCyclicSpace M J Ω x)) :=
  regularGauge (modularCyclicGroup J Ω hsep hcyc x) (modularCyclicGroup_continuous J Ω hsep hcyc x)

def modularCharacterField : unitary
    (Lp (RegularCoreHilbert ℂ) 2 (modularCyclicMeasure (M := M) J Ω x) →L[ℂ]
      Lp (RegularCoreHilbert ℂ) 2 (modularCyclicMeasure (M := M) J Ω x)) :=
  characterField (modularCyclicMeasure (M := M) J Ω x) (fun s => resolventLogFrequency s.val)
    (resolventLogFrequency_measurable.comp measurable_subtype_coe)

theorem cyclicGauge_swap (F : RegularCoreHilbert (ModularCyclicSpace M J Ω x)) :
    l2ScalarSwap volume (modularCyclicMeasure (M := M) J Ω x)
      ((modularCyclicGauge J Ω hsep hcyc x : RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ] RegularCoreHilbert (ModularCyclicSpace M J Ω x)) F) =
    (modularCharacterField (M := M) J Ω x : Lp (RegularCoreHilbert ℂ) 2 (modularCyclicMeasure (M := M) J Ω x) →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 (modularCyclicMeasure (M := M) J Ω x))
      (l2ScalarSwap volume (modularCyclicMeasure (M := M) J Ω x) F) := by
  exact l2ScalarSwap_intertwines_of_tensor (volume : Measure ℝ) (modularCyclicMeasure (M := M) J Ω x)
    (modularCyclicGauge J Ω hsep hcyc x) (modularCharacterField (M := M) J Ω x)
    (cyclicGauge_swap_tensor J Ω hsep hcyc x) F

theorem cyclicGauge_star_swap (F : RegularCoreHilbert (ModularCyclicSpace M J Ω x)) :
    l2ScalarSwap volume (modularCyclicMeasure (M := M) J Ω x)
      ((star (modularCyclicGauge J Ω hsep hcyc x) : RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ] RegularCoreHilbert (ModularCyclicSpace M J Ω x)) F) =
    (star (modularCharacterField (M := M) J Ω x) : Lp (RegularCoreHilbert ℂ) 2 (modularCyclicMeasure (M := M) J Ω x) →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 (modularCyclicMeasure (M := M) J Ω x))
      (l2ScalarSwap volume (modularCyclicMeasure (M := M) J Ω x) F) := by
  exact intertwines_unitary_star
    (l2ScalarSwap (volume : Measure ℝ) (modularCyclicMeasure (M := M) J Ω x)).toContinuousLinearEquiv.toContinuousLinearMap
    (modularCyclicGauge J Ω hsep hcyc x) (modularCharacterField (M := M) J Ω x)
    (cyclicGauge_swap J Ω hsep hcyc x) F

end

end KadisonKastler

end OAI
