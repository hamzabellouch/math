import OAI.InformationTheory.Entanglement.TraceClassModel
import OAI.InformationTheory.Entanglement.HilbertMeasure
import OAI.InformationTheory.Entanglement.LocalMemoryKernels

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder ENNReal MeasureTheory TensorProduct
open ContinuousLinearMap MeasureTheory ProbabilityTheory
namespace SecretKey
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {ι κ υ : Type*}
variable {X : Type*} [MeasurableSpace X]

structure TraceInstrument (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (X : Type*) [MeasurableSpace X] where
  event : Set X → TraceClass b →ₗ[ℂ] TraceClass c
  event_cp : ∀ s, MeasurableSet s → TraceCP b c (event s)
  law : ∀ A : TraceClass b, 0≤(A : H →L[ℂ] H) → PositiveHilbertMeasure X K c
  law_value : ∀ A hA s, MeasurableSet s → (law A hA).value s=event s A
  trace_preserving : ∀ A, traceClassTrace c (event Set.univ A)=traceClassTrace b A
namespace TraceInstrument
variable {b : HilbertBasis ι ℂ H} {c : HilbertBasis κ ℂ K}
variable (I : TraceInstrument b c X)
def outcome (ρ : DensityOperator b) : Measure X := (I.law ρ.val ρ.property.1).traceMeasure
instance outcome_probability (ρ : DensityOperator b) : IsProbabilityMeasure (I.outcome ρ) := by
  let : IsFiniteMeasure (I.outcome ρ) := by unfold outcome; infer_instance
  refine ⟨?_⟩
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
  change (I.law ρ.val ρ.property.1).traceMeasure.real Set.univ=(1 : ℝ≥0∞).toReal
  rw [(I.law ρ.val ρ.property.1).trace_value _ MeasurableSet.univ,
    I.law_value _ _ _ MeasurableSet.univ,← traceClassTrace_re,
    I.trace_preserving,ρ.property.2]
  norm_num
omit [CompleteSpace H] in
lemma outcome_born (ρ : DensityOperator b) {s : Set X} (hs : MeasurableSet s) :
    (I.outcome ρ).real s=(traceClassTrace c (I.event s ρ.val)).re := by
  rw [outcome,(I.law ρ.val ρ.property.1).trace_value _ hs,I.law_value _ _ _ hs,traceClassTrace_re]

structure ConditionalUpdate (ρ : DensityOperator b) where
  state : X → DensityOperator c
  coefficient_measurable : ∀ x y : K,
    Measurable (fun z => inner ℂ x ((state z).val.val y))
  coefficient_integrable : ∀ x y : K,
    Integrable (fun z => inner ℂ x ((state z).val.val y)) (I.outcome ρ)
  disintegration : ∀ s, MeasurableSet s → ∀ x y : K,
    inner ℂ x ((I.event s ρ.val).val y)=
      ∫ z in s, inner ℂ x ((state z).val.val y) ∂I.outcome ρ

def historyKernel {S : Type*} [MeasurableSpace S]
    (J : S → TraceInstrument b c X) (ρ : S → DensityOperator b)
    (hm : ∀ s, MeasurableSet s → Measurable (fun h => (J h).outcome (ρ h) s)) : Kernel S X where
  toFun h := (J h).outcome (ρ h)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    exact hm
instance historyKernel_markov {S : Type*} [MeasurableSpace S]
    (J : S → TraceInstrument b c X) (ρ : S → DensityOperator b)
    (hm : ∀ s, MeasurableSet s → Measurable (fun h => (J h).outcome (ρ h) s)) :
    IsMarkovKernel (historyKernel J ρ hm) := ⟨fun h => inferInstanceAs (IsProbabilityMeasure ((J h).outcome (ρ h)))⟩
end TraceInstrument

section TensorActions
variable {V W V' W' : Type*}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
def tensorFunctional (f : V →ₗ[ℂ] ℂ) (g : W →ₗ[ℂ] ℂ) : V ⊗[ℂ] W →ₗ[ℂ] ℂ :=
  TensorProduct.lift (f.smulRight g)
lemma tensorFunctional_tmul (f : V →ₗ[ℂ] ℂ) (g : W →ₗ[ℂ] ℂ) (x : V) (y : W) :
    tensorFunctional f g (x ⊗ₜ[ℂ] y)=f x*g y := by rfl
lemma local_product_event (f : V' →ₗ[ℂ] ℂ) (g : W →ₗ[ℂ] ℂ)
    (F : V →ₗ[ℂ] V') (x : V) (y : W) :
    tensorFunctional f g (TensorProduct.map F LinearMap.id (x ⊗ₜ[ℂ] y))=f (F x)*g y := by
  rw [TensorProduct.map_tmul,tensorFunctional_tmul,LinearMap.id_apply]
end TensorActions
omit [CompleteSpace H] [CompleteSpace L] in
lemma local_product_born (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (ρ : DensityOperator b) (σ : DensityOperator d) {s : Set X} (hs : MeasurableSet s) :
    (tensorFunctional (traceClassTrace c) (traceClassTrace d)
      (TensorProduct.map (I.event s) LinearMap.id (ρ.val ⊗ₜ[ℂ] σ.val))).re=
      (I.outcome ρ).real s := by
  rw [local_product_event,σ.property.2,mul_one,I.outcome_born ρ hs]

end SecretKey

end

end OAI
