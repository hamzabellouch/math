import Mathlib
import OAI.Analysis.FreeWords.TraceTransferDefinitions
import OAI.Analysis.FreeWords.UltraTrace
import OAI.Analysis.FreeWords.WeakMeanAlgebra

namespace OAI

noncomputable section

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

namespace UniversalStrongKK

open scoped ComplexConjugate InnerProductSpace BoundedContinuousFunction

section OperatorMeanAlgebra

variable {G H : Type*} [TopologicalSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (m : ScalarMean G)

end OperatorMeanAlgebra

end UniversalStrongKK

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

namespace KKTraceTransfer

open scoped BoundedContinuousFunction ComplexOrder InnerProductSpace

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance concreteClosed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  rw [VonNeumannAlgebra.coe_toStarSubalgebra, ← M.centralizer_centralizer]
  exact Set.isClosed_centralizer _

@[instance_reducible] def concreteOrder (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) :=
  CStarAlgebra.spectralOrder _

attribute [local instance] KKTraceTransfer.concreteOrder

@[instance_reducible] def concreteLE (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) :=
  (concreteOrder M).toLE

attribute [local instance] KKTraceTransfer.concreteLE

@[instance_reducible] def concretePreorder (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) :=
  (concreteOrder M).toPreorder

attribute [local instance] KKTraceTransfer.concretePreorder

theorem concreteSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) :=
  CStarAlgebra.spectralOrderedRing _

attribute [local instance] KKTraceTransfer.concreteSOR

@[instance_reducible] def seqOrder (M : VonNeumannAlgebra H) : PartialOrder (ℕ →ᵇ ConcreteAlgebra M) :=
  CStarAlgebra.spectralOrder _

attribute [local instance] KKTraceTransfer.seqOrder

@[instance_reducible] def seqLE (M : VonNeumannAlgebra H) : LE (ℕ →ᵇ ConcreteAlgebra M) :=
  (seqOrder M).toLE

attribute [local instance] KKTraceTransfer.seqLE

@[instance_reducible] def seqPreorder (M : VonNeumannAlgebra H) : Preorder (ℕ →ᵇ ConcreteAlgebra M) :=
  (seqOrder M).toPreorder

attribute [local instance] KKTraceTransfer.seqPreorder

theorem seqSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ℕ →ᵇ ConcreteAlgebra M) :=
  CStarAlgebra.spectralOrderedRing _

attribute [local instance] KKTraceTransfer.seqSOR

def tracePositive {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) :
    ConcreteAlgebra M →ₚ[ℂ] ℂ where
  toLinearMap := τ.map
  monotone' x y h := by
    apply sub_nonneg.mp
    change 0 ≤ τ.map y - τ.map x
    rw [← map_sub]
    apply τ.positive
    obtain ⟨v, hv⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr h)
    rw [hv]
    exact ContinuousLinearMap.isPositive_adjoint_comp_self (v : H →L[ℂ] H)

end

end KKTraceTransfer

namespace KKTraceTransfer

open scoped BoundedContinuousFunction ComplexOrder InnerProductSpace

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance factorBaseConcreteOrder (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) :=
  concreteOrder M

local instance factorBaseConcretePreorder (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) :=
  (concreteOrder M).toPreorder

local instance factorBaseConcreteLE (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) :=
  (concreteOrder M).toLE

local instance factorBaseConcreteSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) :=
  concreteSOR M

def operatorSequence (M : VonNeumannAlgebra H) :
    (ℕ →ᵇ ConcreteAlgebra M) →ₗ[ℂ] (ℕ →ᵇ (H →L[ℂ] H)) where
  toFun x := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun j => (x j : H →L[ℂ] H)) continuous_of_discreteTopology ‖x‖
    (fun j => x.norm_coe_le_norm j)
  map_add' x y := by ext j; rfl
  map_smul' c x := by ext j; rfl

@[simp] theorem operatorSequence_apply {M : VonNeumannAlgebra H}
    (x : ℕ →ᵇ ConcreteAlgebra M) (j : ℕ) : operatorSequence M x j = (x j : H →L[ℂ] H) := rfl

theorem norm_operatorSequence_le {M : VonNeumannAlgebra H} (x : ℕ →ᵇ ConcreteAlgebra M) :
    ‖operatorSequence M x‖ ≤ ‖x‖ := by
  exact (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr fun j => x.norm_coe_le_norm j

def sequenceMean (M : VonNeumannAlgebra H) (ω : Ultrafilter ℕ) :
    (ℕ →ᵇ ConcreteAlgebra M) →ₗ[ℂ] ConcreteAlgebra M where
  toFun x := ⟨UniversalStrongKK.operatorMean (UniversalStrongKK.ultrafilterMean ω)
      (operatorSequence M x), UniversalStrongKK.mem_of_wot_tendsto M
        (UniversalStrongKK.tendsto_operatorMean ω (operatorSequence M x))
        (Filter.Eventually.of_forall fun j => (x j).property)⟩
  map_add' x y := by
    apply Subtype.ext
    exact congrArg (UniversalStrongKK.operatorMean (UniversalStrongKK.ultrafilterMean ω))
      (map_add (operatorSequence M) x y) |>.trans
      (UniversalStrongKK.operatorMean_add _ _ _)
  map_smul' c x := by
    apply Subtype.ext
    exact congrArg (UniversalStrongKK.operatorMean (UniversalStrongKK.ultrafilterMean ω))
      (map_smul (operatorSequence M) c x) |>.trans
      (UniversalStrongKK.operatorMean_smul _ _ _)

theorem norm_sequenceMean_le {M : VonNeumannAlgebra H} (ω : Ultrafilter ℕ)
    (x : ℕ →ᵇ ConcreteAlgebra M) : ‖sequenceMean M ω x‖ ≤ ‖x‖ :=
  (UniversalStrongKK.norm_operatorMean_le _ _).trans (norm_operatorSequence_le x)

theorem tendsto_sequenceMean {M : VonNeumannAlgebra H} (ω : Ultrafilter ℕ)
    (x : ℕ →ᵇ ConcreteAlgebra M) :
    Tendsto (fun j => ContinuousLinearMapWOT.ofCLM (x j : H →L[ℂ] H)) (ω : Filter ℕ)
      (𝓝 (ContinuousLinearMapWOT.ofCLM (sequenceMean M ω x : H →L[ℂ] H))) :=
  UniversalStrongKK.tendsto_operatorMean ω (operatorSequence M x)

theorem trace_sequenceMean {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (ω : Ultrafilter ℕ) (x : ℕ →ᵇ ConcreteAlgebra M) :
    τ.map (sequenceMean M ω x) = KKUltraTrace.ultraTrace (tracePositive τ) ω x := by
  let Aw : WeakAlgebra M := ⟨ContinuousLinearMapWOT.ofCLM (sequenceMean M ω x),
    (sequenceMean M ω x).property⟩
  let Tw : ℕ → WeakAlgebra M := fun j => ⟨ContinuousLinearMapWOT.ofCLM (x j), (x j).property⟩
  have ht : Tendsto Tw (ω : Filter ℕ) (𝓝 Aw) :=
    tendsto_subtype_rng.mpr (tendsto_sequenceMean ω x)
  have ht' : Tendsto Tw (ω : Filter ℕ)
      (𝓝[{T : WeakAlgebra M | ‖T.val.toCLM‖ ≤ ‖x‖}] Aw) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Filter.Eventually.of_forall x.norm_coe_le_norm⟩
  have hτ := (τ.normal ‖x‖ Aw (norm_sequenceMean_le ω x)).tendsto.comp ht'
  exact tendsto_nhds_unique hτ (KKUltraTrace.tendsto_ultraTraceValue (tracePositive τ) ω x)

theorem sequenceMean_const {M : VonNeumannAlgebra H} (ω : Ultrafilter ℕ)
    (a : ConcreteAlgebra M) : sequenceMean M ω (BoundedContinuousFunction.const ℕ a) = a := by
  apply Subtype.ext
  change UniversalStrongKK.operatorMean (UniversalStrongKK.ultrafilterMean ω)
    (operatorSequence M (BoundedContinuousFunction.const ℕ a)) = (a : H →L[ℂ] H)
  rw [show operatorSequence M (BoundedContinuousFunction.const ℕ a) =
    BoundedContinuousFunction.const ℕ (a : H →L[ℂ] H) by ext; rfl]
  exact UniversalStrongKK.operatorMean_const _ _

theorem sequenceMean_bimodule {M : VonNeumannAlgebra H} (ω : Ultrafilter ℕ)
    (a b : ConcreteAlgebra M) (x : ℕ →ᵇ ConcreteAlgebra M) :
    sequenceMean M ω (BoundedContinuousFunction.const ℕ a * x *
      BoundedContinuousFunction.const ℕ b) = a * sequenceMean M ω x * b := by
  apply Subtype.ext
  change UniversalStrongKK.operatorMean (UniversalStrongKK.ultrafilterMean ω)
    (operatorSequence M (BoundedContinuousFunction.const ℕ a * x *
      BoundedContinuousFunction.const ℕ b)) =
    (a : H →L[ℂ] H) * UniversalStrongKK.operatorMean (UniversalStrongKK.ultrafilterMean ω)
      (operatorSequence M x) * (b : H →L[ℂ] H)
  rw [show operatorSequence M (BoundedContinuousFunction.const ℕ a * x *
      BoundedContinuousFunction.const ℕ b) =
    BoundedContinuousFunction.const ℕ (a : H →L[ℂ] H) * operatorSequence M x *
      BoundedContinuousFunction.const ℕ (b : H →L[ℂ] H) by ext; rfl]
  exact UniversalStrongKK.operatorMean_bimodule _ _ _ _

end

end KKTraceTransfer
end

end OAI
