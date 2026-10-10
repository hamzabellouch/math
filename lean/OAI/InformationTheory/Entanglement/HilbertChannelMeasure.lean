import OAI.InformationTheory.Entanglement.HilbertVectorMeasure

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder MeasureTheory
open ContinuousLinearMap MeasureTheory
namespace SecretKey
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι κ T : Type*} [MeasurableSpace T]
namespace TraceChannel
variable {b : HilbertBasis ι ℂ H} {c : HilbertBasis κ ℂ K}
variable (F : TraceChannel b c)
def hermitianApply (A : HermitianTrace b) : HermitianTrace c :=
  ⟨(F.map (HermitianTrace.asTraceClass b A)).val,
    (F.traceNorm_contract (HermitianTrace.asTraceClass b A) (HermitianTrace.property b A)).1⟩
lemma hermitianApply_add (A B : HermitianTrace b) :
    F.hermitianApply (A+B)=F.hermitianApply A+F.hermitianApply B := by
  apply Subtype.ext
  change (F.map (HermitianTrace.asTraceClass b (A+B))).val= _
  rw [HermitianTrace.asTraceClass_add,map_add]
  rfl
lemma hermitianApply_smul (r : ℝ) (A : HermitianTrace b) :
    F.hermitianApply (r • A)=r • F.hermitianApply A := by
  apply Subtype.ext
  change (F.map (HermitianTrace.asTraceClass b (r • A))).val=r • _
  rw [HermitianTrace.asTraceClass_smul,map_smul]
  exact Complex.coe_smul r _
def hermitianLinear : HermitianTrace b →ₗ[ℝ] HermitianTrace c where
  toFun := F.hermitianApply
  map_add' := F.hermitianApply_add
  map_smul' := F.hermitianApply_smul
lemma hermitianLinear_norm (A : HermitianTrace b) : ‖F.hermitianLinear A‖≤1*‖A‖ := by
  change hilbertTraceNorm c (F.map (HermitianTrace.asTraceClass b A)).val≤
    1*hilbertTraceNorm b (HermitianTrace.operator b A)
  simpa only [one_mul,HermitianTrace.asTraceClass_operator] using
    (F.traceNorm_contract (HermitianTrace.asTraceClass b A) (HermitianTrace.property b A)).2

def hermitianMap : HermitianTrace b →L[ℝ] HermitianTrace c :=
  F.hermitianLinear.mkContinuous 1 F.hermitianLinear_norm
lemma hermitianMap_operator (A : HermitianTrace b) :
    HermitianTrace.operator c (F.hermitianMap A)=(F.map (HermitianTrace.asTraceClass b A)).val := rfl
lemma traceValue_asTraceClass (W : PositiveHilbertMeasure T H b)
    {s : Set T} (hs : MeasurableSet s) :
    (HermitianTrace.asTraceClass b (W.traceValue s)).val=W.value s := W.traceValue_operator hs

def onLaw (W : PositiveHilbertMeasure T H b) : PositiveHilbertMeasure T K c where
  value s := HermitianTrace.operator c (F.hermitianMap (W.traceVectorMeasure s))
  coeff x y := W.traceVectorMeasure.mapRange
    (((HermitianTrace.coefficient c x y).comp F.hermitianMap).toLinearMap.toAddMonoidHom)
    ((HermitianTrace.coefficient c x y).comp F.hermitianMap).continuous
  coeff_value x y s hs := rfl
  positive s hs := by
    rw [F.hermitianMap_operator]
    apply F.positive
    change 0≤HermitianTrace.operator b (W.traceValue s)
    rw [W.traceValue_operator hs]
    exact (W.positive s hs).1
  traceMeasure := W.traceMeasure
  traceFinite := inferInstance
  trace_value s hs := by
    rw [F.hermitianMap_operator,F.real_trace]
    change W.traceMeasure.real s=hilbertTrace b (HermitianTrace.operator b (W.traceValue s))
    rw [W.traceValue_operator hs]
    exact W.trace_value s hs
lemma onLaw_value (W : PositiveHilbertMeasure T H b) {s : Set T} (hs : MeasurableSet s) :
    (F.onLaw W).value s=(F.map ⟨W.value s,Submodule.subset_span (W.positive s hs)⟩).val := by
  change (F.map (HermitianTrace.asTraceClass b (W.traceValue s))).val=_
  congr 2
  exact Subtype.ext (W.traceValue_operator hs)
lemma onLaw_traceMeasure (W : PositiveHilbertMeasure T H b) :
    (F.onLaw W).traceMeasure=W.traceMeasure := rfl

theorem onLaw_distance_contract (W V : PositiveHilbertMeasure T H b) :
    hilbertVariation c (fun s => (F.onLaw W).value s-(F.onLaw V).value s)≤
      hilbertVariation b (fun s => W.value s-V.value s) := by
  apply iSup_le; intro P
  apply iSup_le; intro hm
  apply iSup_le; intro hd
  refine le_trans (b := ∑ s∈P, hilbertENorm b (W.value s-V.value s)) ?_ ?_
  swap
  · unfold hilbertVariation
    apply le_iSup_of_le P
    apply le_iSup_of_le hm
    apply le_iSup_of_le hd
    exact le_rfl
  apply Finset.sum_le_sum
  intro s hs
  have hA := (W.positive s (hm s hs))
  have hB := (V.positive s (hm s hs))
  let A : TraceClass b := ⟨W.value s,Submodule.subset_span hA⟩
  let B : TraceClass b := ⟨V.value s,Submodule.subset_span hB⟩
  have ht := (positive_difference_traceClass b hA hB).1
  have hh := F.traceNorm_contract (A-B) ht
  dsimp only
  erw [F.onLaw_value W (hm s hs),F.onLaw_value V (hm s hs)]
  change hilbertENorm c ((F.map A).val-(F.map B).val)≤_
  rw [← Submodule.coe_sub,← map_sub,hilbertENorm_eq c hh.1.2,hilbertENorm_eq b ht.2]
  exact ENNReal.ofReal_le_ofReal hh.2
end TraceChannel

end SecretKey

end

end OAI
