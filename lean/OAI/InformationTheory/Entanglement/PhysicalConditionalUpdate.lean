import OAI.InformationTheory.Entanglement.WeakTensorMeasurable
import OAI.InformationTheory.Entanglement.WeakIntegralForm

namespace OAI

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder MeasureTheory
open ContinuousLinearMap UniformSpace MeasureTheory
namespace SecretKey
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {ι κ υ : Type*}
variable {X : Type*} [MeasurableSpace X]
lemma physical_disintegration_all (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (ρ : DensityOperator b) (σ : DensityOperator d) (U : I.ConditionalUpdate ρ)
    {s : Set X} (hs : MeasurableSet s)
    (G : TraceClass (tensorHilbertBasis b d) →ₗ[ℂ] TraceClass (tensorHilbertBasis c d))
    (hG : IsLeftTraceAction b c d (I.event s) G)
    (x y : HilbertTensor K L) :
    inner ℂ x ((G (densityTensor b d ρ σ).val).val y)=
      ∫ z in s, inner ℂ x ((densityTensor c d (U.state z) σ).val.val y) ∂I.outcome ρ := by
  let R := fun z => densityTensor c d (U.state z) σ
  have hR : ∀ a a', Measurable (fun z => inner ℂ a ((R z).val.val a')) :=
    densityTensor_coefficient_measurable c d U.state (fun _ => σ)
      U.coefficient_measurable (fun _ _ => measurable_const)
  let μ := (I.outcome ρ).restrict s
  let T := (G (densityTensor b d ρ σ).val).val
  have hI (a a') : Integrable (fun z => inner ℂ a ((R z).val.val a')) μ :=
    density_coefficient_integrable (tensorHilbertBasis c d) μ R hR a a'
  have hleft (a : K) (v : L) (z : HilbertTensor K L) :
      inner ℂ z (T (hilbertTmul a v))=∫ t, inner ℂ z ((R t).val.val (hilbertTmul a v)) ∂μ := by
    refine Completion.induction_on z (isClosed_eq (by fun_prop)
      (densityIntegral_left_continuous (tensorHilbertBasis c d) μ R hR _)) ?_
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul p q => exact physical_product_disintegration b c d I ρ σ U hs G hG p a q v
    | add p q hp hq =>
      simp only [Completion.coe_add,inner_add_left,integral_add (hI _ _) (hI _ _),hp,hq]
  change inner ℂ x (T y)=∫ t, inner ℂ x ((R t).val.val y) ∂μ
  refine Completion.induction_on y (isClosed_eq (by fun_prop)
    (densityIntegral_right_continuous (tensorHilbertBasis c d) μ R hR x)) ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul p q => exact hleft p q x
  | add p q hp hq =>
    simp only [Completion.coe_add,map_add,inner_add_right,integral_add (hI _ _) (hI _ _),hp,hq]

lemma physical_product_outcome (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (G : TraceInstrument (tensorHilbertBasis b d) (tensorHilbertBasis c d) X)
    (hG : ∀ s, MeasurableSet s → IsLeftTraceAction b c d (I.event s) (G.event s))
    (ρ : DensityOperator b) (σ : DensityOperator d) :
    G.outcome (densityTensor b d ρ σ)=I.outcome ρ := by
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (G.outcome (densityTensor b d ρ σ)).real s=(I.outcome ρ).real s
  rw [G.outcome_born _ hs]
  exact physical_product_born b c d I ρ σ hs (G.event s) (hG s hs)

def physical_product_update (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (G : TraceInstrument (tensorHilbertBasis b d) (tensorHilbertBasis c d) X)
    (hG : ∀ s, MeasurableSet s → IsLeftTraceAction b c d (I.event s) (G.event s))
    (ρ : DensityOperator b) (σ : DensityOperator d) (U : I.ConditionalUpdate ρ) :
    G.ConditionalUpdate (densityTensor b d ρ σ) where
  state z := densityTensor c d (U.state z) σ
  coefficient_measurable := densityTensor_coefficient_measurable c d U.state (fun _ => σ)
    U.coefficient_measurable (fun _ _ => measurable_const)
  coefficient_integrable x y := by
    rw [physical_product_outcome b c d I G hG ρ σ]
    exact density_coefficient_integrable (tensorHilbertBasis c d) (I.outcome ρ)
      (fun z => densityTensor c d (U.state z) σ)
      (densityTensor_coefficient_measurable c d U.state (fun _ => σ)
        U.coefficient_measurable (fun _ _ => measurable_const)) x y
  disintegration s hs x y := by
    rw [physical_product_outcome b c d I G hG ρ σ]
    exact physical_disintegration_all b c d I ρ σ U hs (G.event s) (hG s hs) x y

end SecretKey

end

end OAI
