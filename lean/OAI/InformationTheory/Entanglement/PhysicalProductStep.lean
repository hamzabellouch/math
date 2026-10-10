import OAI.InformationTheory.Entanglement.TraceTensor
import OAI.InformationTheory.Entanglement.WeakProductPrefix

namespace OAI

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder MeasureTheory
open ContinuousLinearMap UniformSpace MeasureTheory ProbabilityTheory
namespace SecretKey
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {ι κ υ : Type*}
def traceTensorBilinear (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K) :
    TraceClass b →ₗ[ℂ] TraceClass c →ₗ[ℂ] TraceClass (tensorHilbertBasis b c) where
  toFun A :=
    { toFun := traceTensor b c A
      map_add' := fun B C => Subtype.ext (hilbertTensorMap_add_right A.val B.val C.val)
      map_smul' := fun s B => Subtype.ext (hilbertTensorMap_smul_right s A.val B.val) }
  map_add' A B := by
    apply LinearMap.ext
    intro C
    apply Subtype.ext
    exact hilbertTensorMap_add_left A.val B.val C.val
  map_smul' s A := by
    apply LinearMap.ext
    intro B
    apply Subtype.ext
    exact hilbertTensorMap_smul_left s A.val B.val

def traceTensorEmbedding (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K) :
    TraceClass b ⊗[ℂ] TraceClass c →ₗ[ℂ] TraceClass (tensorHilbertBasis b c) :=
  TensorProduct.lift (traceTensorBilinear b c)
@[simp] lemma traceTensorEmbedding_tmul (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (A : TraceClass b) (B : TraceClass c) :
    traceTensorEmbedding b c (A ⊗ₜ[ℂ] B)=traceTensor b c A B := rfl
lemma traceTensorEmbedding_trace (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K) :
    (traceClassTrace (tensorHilbertBasis b c)).comp (traceTensorEmbedding b c)=
      tensorFunctional (traceClassTrace b) (traceClassTrace c) := by
  apply TensorProduct.ext'
  intro A B
  exact traceTensor_trace b c A B
lemma traceTensorEmbedding_coeff (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (x y : H) (u v : K) :
    (traceClassCoefficient (tensorHilbertBasis b c) (hilbertTmul x u) (hilbertTmul y v)).comp
      (traceTensorEmbedding b c)=
      tensorFunctional (traceClassCoefficient b x y) (traceClassCoefficient c u v) := by
  apply TensorProduct.ext'
  intro A B
  change inner ℂ (hilbertTmul x u) (hilbertTensorMap A.val B.val (hilbertTmul y v))=_
  rw [hilbertTensorMap_tmul,hilbertTmul_inner]
  rfl
def densityTensor (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (ρ : DensityOperator b) (σ : DensityOperator c) : DensityOperator (tensorHilbertBasis b c) :=
  ⟨traceTensor b c ρ.val σ.val,hilbertTensorMap_nonneg ρ.property.1 σ.property.1,by
    rw [traceTensor_trace,ρ.property.2,σ.property.2,mul_one]⟩

def IsLeftTraceAction (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (F : TraceClass b →ₗ[ℂ] TraceClass c)
    (G : TraceClass (tensorHilbertBasis b d) →ₗ[ℂ] TraceClass (tensorHilbertBasis c d)) : Prop :=
  ∀ A B, G (traceTensor b d A B)=traceTensor c d (F A) B
lemma leftTraceAction_intertwines (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (F : TraceClass b →ₗ[ℂ] TraceClass c)
    (G : TraceClass (tensorHilbertBasis b d) →ₗ[ℂ] TraceClass (tensorHilbertBasis c d))
    (hG : IsLeftTraceAction b c d F G) :
    G.comp (traceTensorEmbedding b d)=
      (traceTensorEmbedding c d).comp (TensorProduct.map F LinearMap.id) := by
  apply TensorProduct.ext'
  intro A B
  exact hG A B
variable {X : Type*} [MeasurableSpace X]

theorem physical_product_born (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (ρ : DensityOperator b) (σ : DensityOperator d) {s : Set X} (hs : MeasurableSet s)
    (G : TraceClass (tensorHilbertBasis b d) →ₗ[ℂ] TraceClass (tensorHilbertBasis c d))
    (hG : IsLeftTraceAction b c d (I.event s) G) :
    (traceClassTrace (tensorHilbertBasis c d) (G (densityTensor b d ρ σ).val)).re=
      (I.outcome ρ).real s := by
  change (traceClassTrace (tensorHilbertBasis c d) (G (traceTensor b d ρ.val σ.val))).re=_
  rw [hG,traceTensor_trace,σ.property.2,mul_one,I.outcome_born ρ hs]

theorem physical_product_disintegration (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (ρ : DensityOperator b) (σ : DensityOperator d) (U : I.ConditionalUpdate ρ)
    {s : Set X} (hs : MeasurableSet s)
    (G : TraceClass (tensorHilbertBasis b d) →ₗ[ℂ] TraceClass (tensorHilbertBasis c d))
    (hG : IsLeftTraceAction b c d (I.event s) G) (x y : K) (u v : L) :
    inner ℂ (hilbertTmul x u) ((G (densityTensor b d ρ σ).val).val (hilbertTmul y v))=
      ∫ z in s, inner ℂ (hilbertTmul x u)
        ((densityTensor c d (U.state z) σ).val.val (hilbertTmul y v)) ∂I.outcome ρ := by
  change inner ℂ (hilbertTmul x u) ((G (traceTensor b d ρ.val σ.val)).val (hilbertTmul y v))=_
  rw [hG]
  change inner ℂ (hilbertTmul x u) (hilbertTensorMap (I.event s ρ.val).val σ.val.val (hilbertTmul y v))=_
  rw [hilbertTensorMap_tmul,hilbertTmul_inner,U.disintegration s hs]
  erw [← integral_mul_const]
  apply setIntegral_congr_fun hs
  intro z hz
  simp [densityTensor,traceTensor,hilbertTmul_inner]

end SecretKey

end

end OAI
