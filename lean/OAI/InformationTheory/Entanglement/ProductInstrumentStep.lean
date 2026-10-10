import OAI.InformationTheory.Entanglement.TraceInstrument

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder ENNReal MeasureTheory TensorProduct
open ContinuousLinearMap MeasureTheory ProbabilityTheory
namespace SecretKey
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {ι κ υ : Type*} {X : Type*} [MeasurableSpace X]

def traceClassCoefficient (b : HilbertBasis ι ℂ H) (x y : H) : TraceClass b →ₗ[ℂ] ℂ where
  toFun A := inner ℂ x ((A : H →L[ℂ] H) y)
  map_add' A B := by simp
  map_smul' c A := by simp

omit [CompleteSpace H] [CompleteSpace L] in
theorem local_product_disintegration (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (ρ : DensityOperator b) (σ : DensityOperator d)
    (U : I.ConditionalUpdate ρ) {s : Set X} (hs : MeasurableSet s)
    (x y : K) (u v : L) :
    tensorFunctional (traceClassCoefficient c x y) (traceClassCoefficient d u v)
      (TensorProduct.map (I.event s) LinearMap.id (ρ.val ⊗ₜ[ℂ] σ.val))=
    ∫ z in s, tensorFunctional (traceClassCoefficient c x y) (traceClassCoefficient d u v)
      ((U.state z).val ⊗ₜ[ℂ] σ.val) ∂I.outcome ρ := by
  simp only [local_product_event,tensorFunctional_tmul,traceClassCoefficient,LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [U.disintegration s hs x y,integral_mul_const]

omit [CompleteSpace H] [CompleteSpace L] in
theorem right_product_disintegration (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (ρ : DensityOperator b) (σ : DensityOperator d)
    (U : I.ConditionalUpdate ρ) {s : Set X} (hs : MeasurableSet s)
    (x y : K) (u v : L) :
    tensorFunctional (traceClassCoefficient d u v) (traceClassCoefficient c x y)
      (TensorProduct.map LinearMap.id (I.event s) (σ.val ⊗ₜ[ℂ] ρ.val))=
    ∫ z in s, tensorFunctional (traceClassCoefficient d u v) (traceClassCoefficient c x y)
      (σ.val ⊗ₜ[ℂ] (U.state z).val) ∂I.outcome ρ := by
  simp only [TensorProduct.map_tmul,tensorFunctional_tmul,LinearMap.id_apply,
    traceClassCoefficient,LinearMap.coe_mk,AddHom.coe_mk]
  rw [U.disintegration s hs x y,integral_const_mul]

omit [CompleteSpace H] [CompleteSpace L] in
lemma conditional_product_trace (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (ρ : DensityOperator b) (σ : DensityOperator d)
    (U : I.ConditionalUpdate ρ) (z : X) :
    tensorFunctional (traceClassTrace c) (traceClassTrace d)
      ((U.state z).val ⊗ₜ[ℂ] σ.val)=1 := by
  rw [tensorFunctional_tmul,(U.state z).property.2,σ.property.2,mul_one]

end SecretKey

end

end OAI
