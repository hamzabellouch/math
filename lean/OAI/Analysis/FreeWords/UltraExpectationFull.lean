import Mathlib
import OAI.Analysis.FreeWords.UltraExpectation

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

local instance ultraExpectationFullBoundedOrder : PartialOrder (ℕ →ᵇ A) := CStarAlgebra.spectralOrder _

local instance ultraExpectationFullBoundedSOR : StarOrderedRing (ℕ →ᵇ A) := CStarAlgebra.spectralOrderedRing _

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

local instance ultraExpectationFullConcreteOrder (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance ultraExpectationFullConcretePreorder (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance ultraExpectationFullConcreteLE (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance ultraExpectationFullConcreteSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

local instance ultraExpectationFullSeqOrder (M : VonNeumannAlgebra H) : PartialOrder (ℕ →ᵇ ConcreteAlgebra M) := seqOrder M

local instance ultraExpectationFullSeqPreorder (M : VonNeumannAlgebra H) : Preorder (ℕ →ᵇ ConcreteAlgebra M) := (seqOrder M).toPreorder

local instance ultraExpectationFullSeqLE (M : VonNeumannAlgebra H) : LE (ℕ →ᵇ ConcreteAlgebra M) := (seqOrder M).toLE

local instance ultraExpectationFullSeqSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ℕ →ᵇ ConcreteAlgebra M) := seqSOR M

attribute [local instance] KKTraceTransfer.ultraOrder

local instance ultraExpectationFullUltraPreorder {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) :
    Preorder (ultraAlgebra τ ω) := (ultraOrder τ ω).toPreorder

local instance ultraExpectationFullUltraLE {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) :
    LE (ultraAlgebra τ ω) := (ultraOrder τ ω).toLE

local instance ultraExpectationFullUltraSOR {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) :
    type_of% (ultraExpectationUltraSOR τ ω) := ultraExpectationUltraSOR τ ω

def linearSurjDescend {A B C : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    (f : A →ₗ[ℂ] B) (hf : Function.Surjective f) (e : A →ₗ[ℂ] C)
    (he : f.ker ≤ e.ker) : B →ₗ[ℂ] C :=
  (f.ker.liftQ e he).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap

theorem linearSurjDescend_apply {A B C : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    (f : A →ₗ[ℂ] B) (hf : Function.Surjective f) (e : A →ₗ[ℂ] C)
    (he : f.ker ≤ e.ker) (a : A) : linearSurjDescend f hf e he (f a) = e a := by
  change (f.ker.liftQ e he) ((f.quotKerEquivOfSurjective hf).symm (f a)) = e a
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

theorem linearSurjDescend_starAlgHom_apply {A B C : Type*}
    [CStarAlgebra A] [CStarAlgebra B] [AddCommGroup C] [Module ℂ C]
    (f : A →⋆ₐ[ℂ] B) (hf : Function.Surjective f) (e : A →ₗ[ℂ] C)
    (he : f.toAlgHom.toLinearMap.ker ≤ e.ker) (a : A) :
    linearSurjDescend f.toAlgHom.toLinearMap hf e he (f a) = e a :=
  linearSurjDescend_apply f.toAlgHom.toLinearMap hf e he a

def linearSurjDescendStarAlgHomWithSpec {A B C : Type*}
    [CStarAlgebra A] [CStarAlgebra B] [AddCommGroup C] [Module ℂ C]
    (f : A →⋆ₐ[ℂ] B) (hf : Function.Surjective f) (e : A →ₗ[ℂ] C)
    (he : f.toAlgHom.toLinearMap.ker ≤ e.ker) :
    {g : B →ₗ[ℂ] C // ∀ a, g (f a) = e a} :=
  ⟨linearSurjDescend f.toAlgHom.toLinearMap hf e he,
    linearSurjDescend_starAlgHom_apply f hf e he⟩

def ultraExpectationLinearWithSpec {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (ω : Ultrafilter ℕ) :
    {g : ultraAlgebra τ ω →ₗ[ℂ] ConcreteAlgebra M //
      ∀ x, g (ultraProjection τ ω x) = sequenceMean M ω x} :=
  linearSurjDescendStarAlgHomWithSpec (ultraProjection τ ω)
    (ultraProjection_surjective τ ω) (sequenceMean M ω) (fun x hx =>
      sequenceMean_zero_of_projection_zero τ ω x hx)

def ultraExpectationLinear {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (ω : Ultrafilter ℕ) : ultraAlgebra τ ω →ₗ[ℂ] ConcreteAlgebra M :=
  (ultraExpectationLinearWithSpec τ ω).val

@[simp] theorem ultraExpectationLinear_projection {M : VonNeumannAlgebra H}
    (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) (x : ℕ →ᵇ ConcreteAlgebra M) :
    ultraExpectationLinear τ ω (ultraProjection τ ω x) = sequenceMean M ω x :=
  (ultraExpectationLinearWithSpec τ ω).property x

theorem contractive_descend {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    (f : A →⋆ₐ[ℂ] B) (hf : Function.Surjective f) (e : B →ₗ[ℂ] C)
    (he : ∀ a, ‖e (f a)‖ ≤ ‖a‖) (b : B) : ‖e b‖ ≤ ‖b‖ := by
  obtain ⟨x, rfl⟩ := hf b
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨y, hy, hyn⟩ := KKUltraTrace.starHom_controlled_lift f x
    (add_pos_of_nonneg_of_pos (norm_nonneg _) hε) (le_add_of_nonneg_right hε.le)
  calc
    ‖e (f x)‖ = ‖e (f y)‖ := congrArg (fun z => ‖e z‖) hy.symm
    _ ≤ ‖y‖ := he y
    _ ≤ ‖f x‖ + ε := hyn

private theorem contractive_descend_cstar {A B C : Type*}
    [CStarAlgebra A] [CStarAlgebra B] [NormedAddCommGroup C] [NormedSpace ℂ C]
    (f : A →⋆ₐ[ℂ] B) (hf : Function.Surjective f) (e : B →ₗ[ℂ] C)
    (he : ∀ a, ‖e (f a)‖ ≤ ‖a‖) (b : B) : ‖e b‖ ≤ ‖b‖ := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  let := CStarAlgebra.spectralOrder B
  let := CStarAlgebra.spectralOrderedRing B
  exact contractive_descend f hf e he b

theorem ultraExpectationLinear_norm_le {M : VonNeumannAlgebra H}
    (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) (z : ultraAlgebra τ ω) :
    ‖ultraExpectationLinear τ ω z‖ ≤ ‖z‖ :=
  contractive_descend_cstar (ultraProjection τ ω) (ultraProjection_surjective τ ω)
    (ultraExpectationLinear τ ω) (fun a => by
      rw [ultraExpectationLinear_projection]
      exact norm_sequenceMean_le ω a) z

def ultraExpectation {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (ω : Ultrafilter ℕ) : ultraAlgebra τ ω →L[ℂ] ConcreteAlgebra M :=
  (ultraExpectationLinear τ ω).mkContinuous 1 (fun z => by
    simpa only [one_mul] using ultraExpectationLinear_norm_le τ ω z)

@[simp] theorem ultraExpectation_projection {M : VonNeumannAlgebra H}
    (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) (x : ℕ →ᵇ ConcreteAlgebra M) :
    ultraExpectation τ ω (ultraProjection τ ω x) = sequenceMean M ω x :=
  ultraExpectationLinear_projection τ ω x

theorem descend_bimodule {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [CStarAlgebra C] (f : A →⋆ₐ[ℂ] B) (hf : Function.Surjective f)
    (k : C → A) (e : B → C) (m : A → C) (he : ∀ x, e (f x) = m x)
    (hm : ∀ a b x, m (k a * x * k b) = a * m x * b) :
    ∀ a b z, e (f (k a) * z * f (k b)) = a * e z * b := by
  intro a b z
  obtain ⟨x, rfl⟩ := hf z
  rw [← map_mul f, ← map_mul f, he, he]
  exact hm a b x

theorem descend_square {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) (hf : Function.Surjective f)
    (e : B → C) (m : A → C) (he : ∀ x, e (f x) = m x)
    (p : C → Prop) (hm : ∀ x, p (m (star x * x))) : ∀ z, p (e (star z * z)) := by
  intro z
  obtain ⟨x, rfl⟩ := hf z
  rw [← map_star f, ← map_mul f, he]
  exact hm x

theorem ultraExpectation_bimodule {M : VonNeumannAlgebra H}
    (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) :
    ∀ a b x, ultraExpectation τ ω (ultraConstant τ ω a * x * ultraConstant τ ω b) =
      a * ultraExpectation τ ω x * b :=
  descend_bimodule (ultraProjection τ ω) (ultraProjection_surjective τ ω)
    (BoundedContinuousFunction.const ℕ) (ultraExpectation τ ω) (sequenceMean M ω)
    (ultraExpectation_projection τ ω) (sequenceMean_bimodule ω)

theorem ultraExpectation_square {M : VonNeumannAlgebra H}
    (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) :
    ∀ x, ((ultraExpectation τ ω (star x * x) : ConcreteAlgebra M) : H →L[ℂ] H).IsPositive := by
  refine descend_square (ultraProjection τ ω) (ultraProjection_surjective τ ω)
    (ultraExpectation τ ω) (sequenceMean M ω) (ultraExpectation_projection τ ω)
    (fun z : ConcreteAlgebra M => (z : H →L[ℂ] H).IsPositive) ?_
  intro s
  apply UniversalStrongKK.positive_of_wot_tendsto (tendsto_sequenceMean ω (star s*s))
  exact Filter.Eventually.of_forall fun j =>
    ContinuousLinearMap.isPositive_adjoint_comp_self (s j : H →L[ℂ] H)

theorem descend_trace {A B C D : Type*} (f : A → B) (hf : Function.Surjective f)
    (e : B → C) (m : A → C) (he : ∀ x, e (f x) = m x)
    (t : C → D) (r : B → D) (q : A → D)
    (hm : ∀ x, t (m x) = q x) (hr : ∀ x, r (f x) = q x) :
    ∀ z, t (e z) = r z := by
  intro z
  obtain ⟨x, rfl⟩ := hf z
  rw [he, hm, hr]

theorem ultraQuotientState_projection {M : VonNeumannAlgebra H}
    (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) (s : ℕ →ᵇ ConcreteAlgebra M) :
    KKUltraTrace.gnsQuotientState (KKUltraTrace.ultraTrace (tracePositive τ) ω)
      (ultraProjection τ ω s) = KKUltraTrace.ultraTrace (tracePositive τ) ω s :=
  KKUltraTrace.gnsExpectation_image (KKUltraTrace.ultraTrace (tracePositive τ) ω) s

theorem ultraExpectation_trace {M : VonNeumannAlgebra H}
    (τ : FaithfulNormalTrace M) (ω : Ultrafilter ℕ) :
    ∀ x, τ.map (ultraExpectation τ ω x) = KKUltraTrace.gnsQuotientState
      (KKUltraTrace.ultraTrace (tracePositive τ) ω) x :=
  descend_trace (ultraProjection τ ω) (ultraProjection_surjective τ ω)
    (ultraExpectation τ ω) (sequenceMean M ω) (ultraExpectation_projection τ ω)
    τ.map (KKUltraTrace.gnsQuotientState (KKUltraTrace.ultraTrace (tracePositive τ) ω))
    (KKUltraTrace.ultraTrace (tracePositive τ) ω)
    (trace_sequenceMean τ ω) (ultraQuotientState_projection τ ω)

theorem ultra_expectation_exists {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (ω : Ultrafilter ℕ) :
    ∃ E : ultraAlgebra τ ω →L[ℂ] ConcreteAlgebra M,
      (∀ x, ‖E x‖ ≤ ‖x‖) ∧
      (∀ a, E (ultraConstant τ ω a) = a) ∧
      (∀ a b x, E (ultraConstant τ ω a * x * ultraConstant τ ω b) = a * E x * b) ∧
      (∀ x, ((E (star x * x) : ConcreteAlgebra M) : H →L[ℂ] H).IsPositive) ∧
      (∀ x, τ.map (E x) = KKUltraTrace.gnsQuotientState
        (KKUltraTrace.ultraTrace (tracePositive τ) ω) x) ∧
      (∀ x : ℕ →ᵇ ConcreteAlgebra M,
        Filter.Tendsto (fun j => ContinuousLinearMapWOT.ofCLM (x j : H →L[ℂ] H))
          (ω : Filter ℕ) (nhds (ContinuousLinearMapWOT.ofCLM
            (E (ultraProjection τ ω x) : H →L[ℂ] H)))) := by
  refine ⟨ultraExpectation τ ω, ultraExpectationLinear_norm_le τ ω, ?_,
    ultraExpectation_bimodule τ ω, ultraExpectation_square τ ω, ultraExpectation_trace τ ω, ?_⟩
  · intro a
    exact (ultraExpectation_projection τ ω _).trans (sequenceMean_const ω a)
  · intro x
    rw [ultraExpectation_projection]
    exact tendsto_sequenceMean ω x

end

end KKTraceTransfer
end

end OAI
