import Mathlib.MeasureTheory.Integral.Bochner.Set
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralFiniteBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPrincipalIntegralParameter
open MeasureTheory Filter Set

theorem continuousOn_setIntegral_compact
    {P Y : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] [T2Space Y]
    {μ : Measure Y} [IsLocallyFiniteMeasure μ]
    {S : Set P} {T : Set Y} (hS : IsCompact S) (hT : IsCompact T)
    (f : P → Y → ℂ) (hf : ContinuousOn (Function.uncurry f) (S ×ˢ T)) :
    ContinuousOn (fun p => ∫ y in T, f p y ∂μ) S := by
  obtain ⟨B,hB⟩ := (hS.prod hT).bddAbove_image hf.norm
  apply continuousOn_of_dominated (bound:=fun _ => B)
  · intro p hp
    have hs : ContinuousOn (f p) T := hf.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun y hy => ⟨hp,hy⟩)
    exact (hs.integrableOn_compact hT).aestronglyMeasurable
  · intro p hp
    filter_upwards [ae_restrict_mem hT.isClosed.measurableSet] with y hy
    exact hB (mem_image_of_mem _ (show (p,y) ∈ S ×ˢ T from ⟨hp,hy⟩))
  · exact integrableOn_const hT.measure_ne_top
  · filter_upwards [ae_restrict_mem hT.isClosed.measurableSet] with y hy
    exact hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun p hp => ⟨hp,hy⟩)

end Ostmann.Arithmetic.HistoryPrincipalIntegralParameter

end

end OAI
