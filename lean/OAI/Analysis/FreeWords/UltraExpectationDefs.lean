import Mathlib
import OAI.Analysis.FreeWords.FactorBase
import OAI.Analysis.FreeWords.GNSQuotient
import OAI.Analysis.FreeWords.SpectralClip

namespace OAI

noncomputable section

namespace KKUltraTrace

open scoped ComplexOrder BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] KKUltraTrace.seqOrder

attribute [local instance] KKUltraTrace.seqSOR

open scoped InnerProductSpace

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] KKUltraTrace._seqOrder

attribute [local instance] KKUltraTrace._seqSOR

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder BoundedContinuousFunction

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

local instance ultraExpectationDefsPartialOrder : PartialOrder (ℕ →ᵇ A) :=
  CStarAlgebra.spectralOrder _

local instance ultraExpectationDefsStarOrderedRing : StarOrderedRing (ℕ →ᵇ A) :=
  CStarAlgebra.spectralOrderedRing _

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] KKUltraTrace.quotientOrder

attribute [local instance] KKUltraTrace.quotientLE

attribute [local instance] KKUltraTrace.quotientPreorder

attribute [local instance] KKUltraTrace.quotientSOR

end

end KKUltraTrace

open scoped ComplexConjugate InnerProductSpace BoundedContinuousFunction

namespace UniversalStrongKK

section OperatorMean

variable {G H : Type*} [TopologicalSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (m : ScalarMean G)

variable [CompleteSpace H]

end OperatorMean

end UniversalStrongKK

open scoped Topology

namespace UniversalStrongKK

section UltraMean

variable {I : Type*} [TopologicalSpace I]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end UltraMean

end UniversalStrongKK

namespace UniversalStrongKK

open scoped InnerProductSpace

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end UniversalStrongKK

namespace UniversalStrongKK

open scoped ComplexConjugate InnerProductSpace BoundedContinuousFunction

section OperatorMeanAlgebra

variable {G H : Type*} [TopologicalSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (m : ScalarMean G)

end OperatorMeanAlgebra

end UniversalStrongKK

namespace KKTraceTransfer

open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

end KKTraceTransfer

namespace KKTraceTransfer

open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

end KKTraceTransfer

namespace KKTraceTransfer

open scoped BoundedContinuousFunction ComplexOrder InnerProductSpace

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] KKTraceTransfer.concreteOrder

attribute [local instance] KKTraceTransfer.concreteSOR

attribute [local instance] KKTraceTransfer.seqOrder

attribute [local instance] KKTraceTransfer.seqSOR

abbrev ultraAlgebra {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (ω : Ultrafilter ℕ) := KKUltraTrace.gnsQuotient (KKUltraTrace.ultraTrace (tracePositive τ) ω)

def ultraProjection {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) :
    (ℕ →ᵇ ConcreteAlgebra M) →⋆ₐ[ℂ] ultraAlgebra τ ω :=
  (KKUltraTrace.ultraTrace (tracePositive τ) ω).gnsStarAlgHom.codRestrict _
    (fun x => subset_closure ⟨x, rfl⟩)

def ultraConstant {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ)
    (a : ConcreteAlgebra M) : ultraAlgebra τ ω :=
  ultraProjection τ ω (BoundedContinuousFunction.const ℕ a)

end

end KKTraceTransfer
end

end OAI
