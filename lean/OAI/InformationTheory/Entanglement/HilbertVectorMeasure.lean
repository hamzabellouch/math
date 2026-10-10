import OAI.InformationTheory.Entanglement.HermitianInstrument

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder MeasureTheory Function
open ContinuousLinearMap MeasureTheory
namespace SecretKey
attribute [local instance] Classical.propDecidable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι T : Type*} [MeasurableSpace T]
namespace HermitianTrace
variable (b : HilbertBasis ι ℂ H)
def coefficient (x y : H) : HermitianTrace b →L[ℝ] ℂ :=
  ((innerSL ℂ x).restrictScalars ℝ).comp
    (((ContinuousLinearMap.apply ℂ H y).restrictScalars ℝ).comp (inclusion b))
@[simp] lemma coefficient_apply (x y : H) (A : HermitianTrace b) :
    coefficient b x y A=inner ℂ x (operator b A y) := rfl
lemma ext_coefficient {A B : HermitianTrace b}
    (h : ∀ x y, coefficient b x y A=coefficient b x y B) : A=B := by
  apply Subtype.ext
  ext y
  exact ext_inner_left ℂ (fun x => h x y)
end HermitianTrace
namespace PositiveHilbertMeasure
variable {b : HilbertBasis ι ℂ H} (W : PositiveHilbertMeasure T H b)

def traceValue (s : Set T) : HermitianTrace b :=
  if hs : MeasurableSet s then ⟨W.value s,⟨(W.positive s hs).1.isSelfAdjoint,by
    rw [CFC.abs_of_nonneg _ (W.positive s hs).1]
    exact W.positive s hs⟩⟩ else 0
lemma traceValue_operator {s : Set T} (hs : MeasurableSet s) :
    HermitianTrace.operator b (W.traceValue s)=W.value s := by
  simp [traceValue,hs,HermitianTrace.operator]
lemma traceValue_coefficient (x y : H) {s : Set T} (hs : MeasurableSet s) :
    HermitianTrace.coefficient b x y (W.traceValue s)=W.coeff x y s := by
  rw [HermitianTrace.coefficient_apply,W.traceValue_operator hs,W.coeff_value x y s hs]
lemma traceValue_norm {s : Set T} (hs : MeasurableSet s) :
    ‖W.traceValue s‖=W.traceMeasure.real s := by
  rw [HermitianTrace.norm_eq,W.traceValue_operator hs,hilbertTraceNorm,
    CFC.abs_of_nonneg _ (W.positive s hs).1,← W.trace_value s hs]
lemma traceValue_empty : W.traceValue ∅=0 := by
  apply HermitianTrace.ext_coefficient
  intro x y
  rw [W.traceValue_coefficient x y MeasurableSet.empty,VectorMeasure.empty,map_zero]

lemma traceValue_hasSum {f : ℕ→Set T} (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Disjoint on f)) : HasSum (fun i => W.traceValue (f i)) (W.traceValue (⋃ i, f i)) := by
  have hs : Summable (fun i => W.traceValue (f i)) := by
    apply Summable.of_norm
    simpa only [W.traceValue_norm (hf _)] using (summable_measure_toReal (μ := W.traceMeasure) hf hd)
  convert hs.hasSum using 1
  apply HermitianTrace.ext_coefficient
  intro x y
  have h1 := hs.hasSum.mapL (HermitianTrace.coefficient b x y)
  have h2 := (W.coeff x y).m_iUnion hf hd
  simp only [W.traceValue_coefficient x y (hf _)] at h1
  rw [W.traceValue_coefficient x y (MeasurableSet.iUnion hf)]
  exact h2.unique h1

def traceVectorMeasure : VectorMeasure T (HermitianTrace b) where
  measureOf' := W.traceValue
  empty' := W.traceValue_empty
  not_measurable' := by intro s hs; simp [traceValue,hs]
  m_iUnion' := by intro f hf hd; exact W.traceValue_hasSum hf hd
@[simp] lemma traceVectorMeasure_apply (s : Set T) : W.traceVectorMeasure s=W.traceValue s := rfl
lemma traceVectorMeasure_coefficient (x y : H) {s : Set T} (hs : MeasurableSet s) :
    HermitianTrace.coefficient b x y (W.traceVectorMeasure s)=W.coeff x y s :=
  W.traceValue_coefficient x y hs
end PositiveHilbertMeasure

end SecretKey

end

end OAI
