import OAI.Analysis.KadisonKastler.ModularGaugeTransport
import OAI.Analysis.KadisonKastler.ResolventSqrtCalculus
import OAI.Analysis.KadisonKastler.TomitaPolarCorePairing

namespace OAI

/-! # Common spectral coordinates for the two trace-boundary vectors

The algebra vector and its conjugate adjoint use square-root weights
in one cyclic resolvent model. These coordinates let the clipped
exponential translation law be applied to both sides of a monomial.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

def coreTraceLeftCoordinate (a : Algebra M) :
    ModularCyclicSpace M J Ω (tomitaCoreCoordinate J Ω hsep hcyc a) :=
  ContinuousMap.toLp 2
    (modularCyclicMeasure (M := M) J Ω (tomitaCoreCoordinate J Ω hsep hcyc a)) ℂ
    (resolventSqrtFunction (graphResolvent M J Ω 1))

def coreTraceRightCoordinate (a : Algebra M) :
    ModularCyclicSpace M J Ω (tomitaCoreCoordinate J Ω hsep hcyc a) :=
  ContinuousMap.toLp 2
    (modularCyclicMeasure (M := M) J Ω (tomitaCoreCoordinate J Ω hsep hcyc a)) ℂ
    (resolventComplementSqrtFunction (graphResolvent M J Ω 1))

omit [TopologicalSpace.SeparableSpace H] in
theorem coreTraceLeftCoordinate_embedding (a : Algebra M) :
    modularCyclicEmbedding J Ω (tomitaCoreCoordinate J Ω hsep hcyc a)
      (coreTraceLeftCoordinate J Ω hsep hcyc a) = a.val Ω := by
  change resolventCyclicIsometry (graphResolvent M J Ω 1)
    (graphResolvent_positive J Ω 1).isSelfAdjoint _
      (ContinuousMap.toLp 2 _ ℂ (resolventSqrtFunction _)) = _
  rw [resolventCyclicIsometry_continuous,
    resolventContinuousCalculus_sqrt _ _
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr (graphResolvent_positive J Ω 1))]
  exact tomitaCoreCoordinate_first J Ω hsep hcyc a

omit [TopologicalSpace.SeparableSpace H] in
theorem coreTraceRightCoordinate_embedding (a : Algebra M) :
    modularCyclicEmbedding J Ω (tomitaCoreCoordinate J Ω hsep hcyc a)
      (coreTraceRightCoordinate J Ω hsep hcyc a) =
      tomitaPolarConjugation J Ω hsep hcyc (star a.val Ω) := by
  have hq : 0 ≤ 1 - graphResolvent M J Ω 1 := by
    rw [← tomitaGraphComplementRoot_square J Ω hsep hcyc]
    have hs := (tomitaGraphComplementRoot_nonneg (M := M) J Ω).isSelfAdjoint
    simpa only [hs.star_eq] using
      (star_mul_self_nonneg (tomitaGraphComplementRoot (M := M) J Ω))
  change resolventCyclicIsometry (graphResolvent M J Ω 1)
    (graphResolvent_positive J Ω 1).isSelfAdjoint _
      (ContinuousMap.toLp 2 _ ℂ (resolventComplementSqrtFunction _)) = _
  rw [resolventCyclicIsometry_continuous, resolventContinuousCalculus_complement_sqrt _ _ hq]
  exact tomitaCoreCoordinate_complement J Ω hsep hcyc a

end

end KadisonKastler

end OAI
