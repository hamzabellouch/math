import OAI.InformationTheory.Entanglement.HermitianBanach
import OAI.InformationTheory.Entanglement.InstrumentContraction

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder MeasureTheory
open ContinuousLinearMap MeasureTheory
namespace SecretKey
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι κ : Type*}
namespace HermitianTrace
variable (b : HilbertBasis ι ℂ H)
def asTraceClass (A : HermitianTrace b) : TraceClass b :=
  ⟨operator b A,by
    obtain ⟨hp,hn⟩ := hermitian_parts_finite b (property b A)
    rw [← CFC.posPart_sub_negPart (operator b A) (property b A).1]
    exact (traceClassSpace b).sub_mem (Submodule.subset_span hp) (Submodule.subset_span hn)⟩
@[simp] lemma asTraceClass_operator (A : HermitianTrace b) : (asTraceClass b A).val=operator b A := rfl
@[simp] lemma asTraceClass_add (A B : HermitianTrace b) : asTraceClass b (A+B)=asTraceClass b A+asTraceClass b B := rfl
@[simp] lemma asTraceClass_smul (s : ℝ) (A : HermitianTrace b) :
    asTraceClass b (s • A)=(s : ℂ) • asTraceClass b A := by
  apply Subtype.ext
  exact (Complex.coe_smul s (operator b A)).symm
instance : MeasurableSpace (HermitianTrace b) := borel _
instance : BorelSpace (HermitianTrace b) := ⟨rfl⟩
end HermitianTrace
variable {X : Type*} [MeasurableSpace X]
namespace TraceInstrument
variable {b : HilbertBasis ι ℂ H} {c : HilbertBasis κ ℂ K}
variable (I : TraceInstrument b c X)
omit [CompleteSpace H] in
lemma event_positive_trace_bound (A : TraceClass b) (hA : 0≤A.val)
    {s : Set X} (hs : MeasurableSet s) :
    HasFinitePositiveTrace c (I.event s A).val ∧
      hilbertTrace c (I.event s A).val≤hilbertTrace b A.val := by
  have hp := (traceClass_positive_iff c _).mp
    ⟨(I.event s A).property,cp_trace_positive b c (I.event_cp s hs) hA⟩
  refine ⟨hp,?_⟩
  rw [← I.law_value A hA s hs,← (I.law A hA).trace_value s hs]
  have hm : (I.law A hA).traceMeasure.real s≤(I.law A hA).traceMeasure.real Set.univ := by
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ s))
  apply hm.trans_eq
  rw [(I.law A hA).trace_value _ MeasurableSet.univ,I.law_value _ _ _ MeasurableSet.univ,
    ← traceClassTrace_re,I.trace_preserving,traceClassTrace_re]

lemma event_traceNorm_bound (A : TraceClass b) (hA : HermitianTraceClass b A.val)
    {s : Set X} (hs : MeasurableSet s) :
    HermitianTraceClass c (I.event s A).val ∧
      hilbertTraceNorm c (I.event s A).val≤hilbertTraceNorm b A.val := by
  obtain ⟨hp,hn⟩ := hermitian_parts_finite b hA
  let P : TraceClass b := ⟨posPart A.val,Submodule.subset_span hp⟩
  let N : TraceClass b := ⟨negPart A.val,Submodule.subset_span hn⟩
  have he : P-N=A := Subtype.ext (CFC.posPart_sub_negPart _ hA.1)
  have hp' := I.event_positive_trace_bound P hp.1 hs
  have hn' := I.event_positive_trace_bound N hn.1 hs
  have hh := positive_difference_traceClass c hp'.1 hn'.1
  have heF : (I.event s A).val=(I.event s P).val-(I.event s N).val := by
    rw [← Submodule.coe_sub,← map_sub,he]
  rw [← heF] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  rw [hilbertTraceNorm_jordan b hA]
  exact add_le_add hp'.2 hn'.2
def hermitianEventApply (s : Set X) (hs : MeasurableSet s) (A : HermitianTrace b) :
    HermitianTrace c := by
  refine ⟨(I.event s (HermitianTrace.asTraceClass b A)).val,?_⟩
  change HermitianTraceClass c (I.event s (HermitianTrace.asTraceClass b A)).val
  exact (I.event_traceNorm_bound (HermitianTrace.asTraceClass b A)
    (HermitianTrace.property b A) hs).1
lemma hermitianEventApply_add (s : Set X) (hs : MeasurableSet s) (A B : HermitianTrace b) :
    I.hermitianEventApply s hs (A+B)=I.hermitianEventApply s hs A+I.hermitianEventApply s hs B := by
  apply Subtype.ext
  change (I.event s (HermitianTrace.asTraceClass b (A+B))).val=
    (I.event s (HermitianTrace.asTraceClass b A)).val+(I.event s (HermitianTrace.asTraceClass b B)).val
  rw [HermitianTrace.asTraceClass_add,map_add]
  rfl
lemma hermitianEventApply_smul (s : Set X) (hs : MeasurableSet s) (r : ℝ) (A : HermitianTrace b) :
    I.hermitianEventApply s hs (r • A)=r • I.hermitianEventApply s hs A := by
  apply Subtype.ext
  change (I.event s (HermitianTrace.asTraceClass b (r • A))).val=
    r • (I.event s (HermitianTrace.asTraceClass b A)).val
  rw [HermitianTrace.asTraceClass_smul,map_smul]
  exact Complex.coe_smul r _
def hermitianEventLinear (s : Set X) (hs : MeasurableSet s) : HermitianTrace b →ₗ[ℝ] HermitianTrace c where
  toFun := I.hermitianEventApply s hs
  map_add' := I.hermitianEventApply_add s hs
  map_smul' := I.hermitianEventApply_smul s hs
lemma hermitianEventLinear_norm (s : Set X) (hs : MeasurableSet s) (A : HermitianTrace b) :
    ‖I.hermitianEventLinear s hs A‖≤1*‖A‖ := by
  change hilbertTraceNorm c (I.event s (HermitianTrace.asTraceClass b A)).val≤
    1*hilbertTraceNorm b (HermitianTrace.operator b A)
  simpa only [one_mul,HermitianTrace.asTraceClass_operator] using (I.event_traceNorm_bound (HermitianTrace.asTraceClass b A)
    (HermitianTrace.property b A) hs).2

def hermitianEvent (s : Set X) (hs : MeasurableSet s) :
    HermitianTrace b →L[ℝ] HermitianTrace c :=
  (I.hermitianEventLinear s hs).mkContinuous 1 (I.hermitianEventLinear_norm s hs)

lemma event_integral {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (f : S→HermitianTrace b) (hf : Integrable f μ) {s : Set X} (hs : MeasurableSet s) :
    I.hermitianEvent s hs (∫ h, f h ∂μ)=∫ h, I.hermitianEvent s hs (f h) ∂μ := by
  exact ((I.hermitianEvent s hs).integral_comp_comm hf).symm
end TraceInstrument

end SecretKey

end

end OAI
