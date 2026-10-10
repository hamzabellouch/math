import OAI.InformationTheory.Entanglement.WeakStateUnique

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder MeasureTheory
open ContinuousLinearMap MeasureTheory
namespace SecretKey
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {ι κ υ X : Type*} [MeasurableSpace X]

theorem physical_product_version (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (G : TraceInstrument (tensorHilbertBasis b d) (tensorHilbertBasis c d) X)
    (hG : ∀ s, MeasurableSet s → IsLeftTraceAction b c d (I.event s) (G.event s))
    (ρ : DensityOperator b) (σ : DensityOperator d) (U : I.ConditionalUpdate ρ)
    (V : G.ConditionalUpdate (densityTensor b d ρ σ)) :
    V.state=ᵐ[G.outcome (densityTensor b d ρ σ)]
      (fun z => densityTensor c d (U.state z) σ) :=
  V.ae_unique (physical_product_update b c d I G hG ρ σ U)

end SecretKey

end

end OAI
