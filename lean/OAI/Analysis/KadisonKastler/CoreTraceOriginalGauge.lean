import OAI.Analysis.KadisonKastler.CyclicSqrtGaugeBalance
import OAI.Analysis.KadisonKastler.GaugeWindowTransport
import OAI.Analysis.KadisonKastler.FrequencyPacketTensor

namespace OAI

/-! # The trace balance in the original modular representation -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem compLp_regularFrequencyPacket (L : H →L[ℂ] K)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v : H) :
    L.compLp (regularFrequencyPacket f v) = regularFrequencyPacket f (L v) := by
  rw [regularFrequencyPacket_eq_scalarLpTensor (H := H),
    regularFrequencyPacket_eq_scalarLpTensor (H := K)]
  exact compLp_scalarLpTensor volume L _ v

variable [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem coreTraceRoot_gauge_balance (x : H) :
    regularFrequencyWindow 0 1
      ((star (regularGauge (modularStrongGroup J Ω hsep hcyc)
        (modularStrongGroup_continuous J Ω hsep hcyc)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularFrequencyPacket coreTraceFrequencyScalar ((modularCyclicEmbedding (M := M) J Ω x) (cyclicLeftRootVector (M := M) J Ω x)))) =
    (star (regularGauge (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyWindow 0 1
        ((regularGauge (modularStrongGroup J Ω hsep hcyc)
          (modularStrongGroup_continuous J Ω hsep hcyc) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
          (regularFrequencyPacket coreTraceFrequencyScalar
            ((modularCyclicEmbedding (M := M) J Ω x) (cyclicRightRootVector (M := M) J Ω x))))) := by
  let L := modularCyclicEmbedding (M := M) J Ω x
  have h := regularGauge_window_balance_transport
    (H := ModularCyclicSpace M J Ω x) (K := H) L
    (modularCyclicGroup J Ω hsep hcyc x) (modularStrongGroup J Ω hsep hcyc)
    (modularCyclicGroup_continuous J Ω hsep hcyc x)
    (modularStrongGroup_continuous J Ω hsep hcyc)
    (modularCyclicEmbedding_group J Ω hsep hcyc x)
    ((Lp.fourierTransformₗᵢ ℝ ℂ).symm coreTraceFrequencyScalar)
    (cyclicLeftRootVector (M := M) J Ω x) (cyclicRightRootVector (M := M) J Ω x)
    (cyclicSqrtGaugeBalance (M := M) J Ω hsep hcyc x)
  rw [← regularFrequencyPacket_eq_scalarLpTensor (H := H),
    ← regularFrequencyPacket_eq_scalarLpTensor (H := H)] at h
  exact h

theorem coreTraceOriginal_gauge_balance (a : Algebra M) :
    regularFrequencyWindow 0 1
      ((star (regularGauge (modularStrongGroup J Ω hsep hcyc)
        (modularStrongGroup_continuous J Ω hsep hcyc)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularFrequencyPacket coreTraceFrequencyScalar (a.val Ω))) =
    (star (regularGauge (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyWindow 0 1
        ((regularGauge (modularStrongGroup J Ω hsep hcyc)
          (modularStrongGroup_continuous J Ω hsep hcyc) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
          (regularFrequencyPacket coreTraceFrequencyScalar
            (tomitaPolarConjugation J Ω hsep hcyc (star a.val Ω))))) := by
  let x := tomitaCoreCoordinate J Ω hsep hcyc a
  have hl : modularCyclicEmbedding (M := M) J Ω x
      (cyclicLeftRootVector (M := M) J Ω x) = a.val Ω := by
    exact coreTraceLeftCoordinate_embedding J Ω hsep hcyc a
  have hr : modularCyclicEmbedding (M := M) J Ω x
      (cyclicRightRootVector (M := M) J Ω x) =
      tomitaPolarConjugation J Ω hsep hcyc (star a.val Ω) := by
    exact coreTraceRightCoordinate_embedding J Ω hsep hcyc a
  have h := coreTraceRoot_gauge_balance (M := M) J Ω hsep hcyc x
  rw [hl, hr] at h
  exact h

end

end KadisonKastler

end OAI
