import OAI.InformationTheory.Entanglement.PhysicalAdaptiveStep

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

def IsRightTraceAction (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (F : TraceClass b →ₗ[ℂ] TraceClass c)
    (G : TraceClass (tensorHilbertBasis d b) →ₗ[ℂ] TraceClass (tensorHilbertBasis d c)) : Prop :=
  ∀ A B, G (traceTensor d b B A)=traceTensor d c B (F A)
variable {X : Type*} [MeasurableSpace X]
lemma physical_right_born (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (ρ : DensityOperator b) (σ : DensityOperator d) {s : Set X} (hs : MeasurableSet s)
    (G : TraceClass (tensorHilbertBasis d b) →ₗ[ℂ] TraceClass (tensorHilbertBasis d c))
    (hG : IsRightTraceAction b c d (I.event s) G) :
    (traceClassTrace (tensorHilbertBasis d c) (G (densityTensor d b σ ρ).val)).re=
      (I.outcome ρ).real s := by
  change (traceClassTrace (tensorHilbertBasis d c) (G (traceTensor d b σ.val ρ.val))).re=_
  rw [hG,traceTensor_trace,σ.property.2,one_mul,I.outcome_born ρ hs]
lemma physical_right_disintegration (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (ρ : DensityOperator b) (σ : DensityOperator d) (U : I.ConditionalUpdate ρ)
    {s : Set X} (hs : MeasurableSet s)
    (G : TraceClass (tensorHilbertBasis d b) →ₗ[ℂ] TraceClass (tensorHilbertBasis d c))
    (hG : IsRightTraceAction b c d (I.event s) G) (x y : K) (u v : L) :
    inner ℂ (hilbertTmul u x) ((G (densityTensor d b σ ρ).val).val (hilbertTmul v y))=
      ∫ z in s, inner ℂ (hilbertTmul u x)
        ((densityTensor d c σ (U.state z)).val.val (hilbertTmul v y)) ∂I.outcome ρ := by
  change inner ℂ (hilbertTmul u x) ((G (traceTensor d b σ.val ρ.val)).val (hilbertTmul v y))=_
  rw [hG]
  change inner ℂ (hilbertTmul u x) (hilbertTensorMap σ.val.val (I.event s ρ.val).val (hilbertTmul v y))=_
  rw [hilbertTensorMap_tmul,hilbertTmul_inner,U.disintegration s hs]
  erw [← integral_const_mul]
  apply setIntegral_congr_fun hs
  intro z hz
  simp [densityTensor,traceTensor,hilbertTmul_inner]
lemma physical_right_disintegration_all (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (ρ : DensityOperator b) (σ : DensityOperator d) (U : I.ConditionalUpdate ρ)
    {s : Set X} (hs : MeasurableSet s)
    (G : TraceClass (tensorHilbertBasis d b) →ₗ[ℂ] TraceClass (tensorHilbertBasis d c))
    (hG : IsRightTraceAction b c d (I.event s) G)
    (x y : HilbertTensor L K) :
    inner ℂ x ((G (densityTensor d b σ ρ).val).val y)=
      ∫ z in s, inner ℂ x ((densityTensor d c σ (U.state z)).val.val y) ∂I.outcome ρ := by
  let R := fun z => densityTensor d c σ (U.state z)
  have hR : ∀ a a', Measurable (fun z => inner ℂ a ((R z).val.val a')) :=
    densityTensor_coefficient_measurable d c (fun _ => σ) U.state
      (fun _ _ => measurable_const) U.coefficient_measurable
  let μ := (I.outcome ρ).restrict s
  let T := (G (densityTensor d b σ ρ).val).val
  have hI (a a') : Integrable (fun z => inner ℂ a ((R z).val.val a')) μ :=
    density_coefficient_integrable (tensorHilbertBasis d c) μ R hR a a'
  have hleft (a : L) (v : K) (z : HilbertTensor L K) :
      inner ℂ z (T (hilbertTmul a v))=∫ t, inner ℂ z ((R t).val.val (hilbertTmul a v)) ∂μ := by
    refine Completion.induction_on z (isClosed_eq (by fun_prop)
      (densityIntegral_left_continuous (tensorHilbertBasis d c) μ R hR _)) ?_
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul p q => exact physical_right_disintegration b c d I ρ σ U hs G hG q v p a
    | add p q hp hq =>
      simp only [Completion.coe_add,inner_add_left,integral_add (hI _ _) (hI _ _),hp,hq]
  change inner ℂ x (T y)=∫ t, inner ℂ x ((R t).val.val y) ∂μ
  refine Completion.induction_on y (isClosed_eq (by fun_prop)
    (densityIntegral_right_continuous (tensorHilbertBasis d c) μ R hR x)) ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul p q => exact hleft p q x
  | add p q hp hq =>
    simp only [Completion.coe_add,map_add,inner_add_right,integral_add (hI _ _) (hI _ _),hp,hq]

lemma physical_right_outcome (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (G : TraceInstrument (tensorHilbertBasis d b) (tensorHilbertBasis d c) X)
    (hG : ∀ s, MeasurableSet s → IsRightTraceAction b c d (I.event s) (G.event s))
    (ρ : DensityOperator b) (σ : DensityOperator d) :
    G.outcome (densityTensor d b σ ρ)=I.outcome ρ := by
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (G.outcome (densityTensor d b σ ρ)).real s=(I.outcome ρ).real s
  rw [G.outcome_born _ hs]
  exact physical_right_born b c d I ρ σ hs (G.event s) (hG s hs)

def physical_right_update (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (G : TraceInstrument (tensorHilbertBasis d b) (tensorHilbertBasis d c) X)
    (hG : ∀ s, MeasurableSet s → IsRightTraceAction b c d (I.event s) (G.event s))
    (ρ : DensityOperator b) (σ : DensityOperator d) (U : I.ConditionalUpdate ρ) :
    G.ConditionalUpdate (densityTensor d b σ ρ) where
  state z := densityTensor d c σ (U.state z)
  coefficient_measurable := densityTensor_coefficient_measurable d c (fun _ => σ) U.state
    (fun _ _ => measurable_const) U.coefficient_measurable
  coefficient_integrable x y := by
    rw [physical_right_outcome b c d I G hG ρ σ]
    exact density_coefficient_integrable (tensorHilbertBasis d c) (I.outcome ρ)
      (fun z => densityTensor d c σ (U.state z))
      (densityTensor_coefficient_measurable d c (fun _ => σ) U.state
        (fun _ _ => measurable_const) U.coefficient_measurable) x y
  disintegration s hs x y := by
    rw [physical_right_outcome b c d I G hG ρ σ]
    exact physical_right_disintegration_all b c d I ρ σ U hs (G.event s) (hG s hs) x y

end SecretKey

end

end OAI
