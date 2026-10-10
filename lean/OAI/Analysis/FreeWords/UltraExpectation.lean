import Mathlib
import OAI.Analysis.FreeWords.TraceTransfer
import OAI.Analysis.FreeWords.UltraExpectationDefs
import OAI.Analysis.FreeWords.UltraQuotientRange

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

local instance ultraExpectationSeqOrder : PartialOrder (ℕ →ᵇ A) := CStarAlgebra.spectralOrder _

local instance ultraExpectationSeqSOR : StarOrderedRing (ℕ →ᵇ A) := CStarAlgebra.spectralOrderedRing _

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

attribute [local instance] KKTraceTransfer.concreteLE

attribute [local instance] KKTraceTransfer.concretePreorder

attribute [local instance] KKTraceTransfer.concreteSOR

attribute [local instance] KKTraceTransfer.seqOrder

attribute [local instance] KKTraceTransfer.seqLE

attribute [local instance] KKTraceTransfer.seqPreorder

attribute [local instance] KKTraceTransfer.seqSOR

end

end KKTraceTransfer

namespace KKTraceTransfer

open scoped BoundedContinuousFunction ComplexOrder InnerProductSpace

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance ultraExpectationConcreteOrder (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance ultraExpectationConcretePreorder (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance ultraExpectationConcreteLE (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance ultraExpectationConcreteSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

local instance ultraExpectationConcreteSeqOrder (M : VonNeumannAlgebra H) : PartialOrder (ℕ →ᵇ ConcreteAlgebra M) := seqOrder M

local instance ultraExpectationConcreteSeqPreorder (M : VonNeumannAlgebra H) : Preorder (ℕ →ᵇ ConcreteAlgebra M) := (seqOrder M).toPreorder

local instance ultraExpectationConcreteSeqLE (M : VonNeumannAlgebra H) : LE (ℕ →ᵇ ConcreteAlgebra M) := (seqOrder M).toLE

local instance ultraExpectationConcreteSeqSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ℕ →ᵇ ConcreteAlgebra M) := seqSOR M

@[instance_reducible] def ultraOrder {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) :
    PartialOrder (ultraAlgebra τ ω) := CStarAlgebra.spectralOrder _

attribute [local instance] KKTraceTransfer.ultraOrder

local instance ultraExpectationUltraPreorder {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) :
    Preorder (ultraAlgebra τ ω) := (ultraOrder τ ω).toPreorder

local instance ultraExpectationUltraLE {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) :
    LE (ultraAlgebra τ ω) := (ultraOrder τ ω).toLE

local instance ultraExpectationUltraSOR {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) :
    type_of% (CStarAlgebra.spectralOrderedRing (ultraAlgebra τ ω)) :=
  CStarAlgebra.spectralOrderedRing (ultraAlgebra τ ω)

private theorem closure_range_surjective {A B : Type*} [TopologicalSpace B]
    (f : A → B) (hclosed : IsClosed (Set.range f)) :
    Function.Surjective (fun x : A =>
      (⟨f x, subset_closure ⟨x, rfl⟩⟩ : closure (Set.range f))) := by
  rintro ⟨y, hy⟩
  rw [hclosed.closure_eq] at hy
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

theorem ultraProjection_surjective {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (ω : Ultrafilter ℕ) : Function.Surjective (ultraProjection τ ω) :=
  closure_range_surjective (KKUltraTrace.ultraTrace (tracePositive τ) ω).gnsStarAlgHom
    (KKUltraTrace.ultra_gns_image_closed (tracePositive τ) ω)

private theorem trace_star_mul_zero_of_gns_zero {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ) (x : A)
    (hx : τ.gnsStarAlgHom x = 0) : τ (star x * x) = 0 := by
  rw [← KKUltraTrace.gnsExpectation_image, map_mul, map_star, hx, star_zero, mul_zero]
  simp [KKUltraTrace.gnsExpectation]

theorem sequenceMean_zero_of_projection_zero {M : VonNeumannAlgebra H}
    (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) (x : ℕ →ᵇ ConcreteAlgebra M)
    (hx : ultraProjection τ ω x = 0) : sequenceMean M ω x = 0 := by
  have h0 : KKUltraTrace.ultraTrace (tracePositive τ) ω (star x * x) = 0 := by
    have hh : (KKUltraTrace.ultraTrace (tracePositive τ) ω).gnsStarAlgHom x = 0 :=
      congrArg Subtype.val hx
    exact trace_star_mul_zero_of_gns_zero (KKUltraTrace.ultraTrace (tracePositive τ) ω) x hh
  have ht := KKUltraTrace.tendsto_ultraTraceValue (tracePositive τ) ω (star x * x)
  change Tendsto (fun j => τ.map (star (x j) * x j)) (ω : Filter ℕ)
    (𝓝 (KKUltraTrace.ultraTrace (tracePositive τ) ω (star x*x))) at ht
  rw [h0] at ht
  have htn : Tendsto (fun j => traceNorm τ (x j)) (ω : Filter ℕ) (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp
      (Complex.continuous_re.continuousAt.tendsto.comp ht)
    simpa only [traceNorm, Complex.zero_re, Real.sqrt_zero, Function.comp_def] using hh
  have hs (ξ : H) := trace_transfer τ ω x ⟨‖x‖, x.norm_coe_le_norm⟩ htn ξ
  have hstrong (ξ : H) : Tendsto (fun j => (x j : H →L[ℂ] H) ξ) (ω : Filter ℕ) (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).mpr (hs ξ)
  have hweak : Tendsto (fun j => ContinuousLinearMapWOT.ofCLM (x j : H →L[ℂ] H))
      (ω : Filter ℕ) (𝓝 0) := by
    apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
    intro ξ η
    simpa using tendsto_const_nhds.inner (hstrong ξ)
  have heq := tendsto_nhds_unique (tendsto_sequenceMean ω x) hweak
  apply Subtype.ext
  exact congrArg ContinuousLinearMapWOT.toCLM heq

end

end KKTraceTransfer
end

end OAI
