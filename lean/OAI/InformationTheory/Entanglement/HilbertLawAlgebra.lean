import OAI.InformationTheory.Entanglement.HilbertLawMetric

namespace OAI

noncomputable section
open scoped BigOperators ENNReal MeasureTheory InnerProductSpace ComplexOrder
open MeasureTheory ContinuousLinearMap
namespace SecretKey
variable {T : Type*} [MeasurableSpace T]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι a : Type*}
omit [CompleteSpace H] in
lemma finitePositiveTrace_sum (b : HilbertBasis ι ℂ H) (s : Finset a) (A : a→H→L[ℂ]H)
    (hA : ∀ i∈s, HasFinitePositiveTrace b (A i)) : HasFinitePositiveTrace b (∑ i∈s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact ⟨le_rfl,by simp⟩
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact finitePositiveTrace_add b (hA i (by simp)) (ih (fun j hj => hA j (by simp [hj])))
lemma hermitianTraceClass_sum (b : HilbertBasis ι ℂ H) (s : Finset a) (A : a→H→L[ℂ]H)
    (hA : ∀ i∈s, HermitianTraceClass b (A i)) : HermitianTraceClass b (∑ i∈s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact ⟨by simp,by simp [HasFinitePositiveTrace]⟩
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hilbertTraceNorm_triangle b (hA i (by simp)) (ih (fun j hj => hA j (by simp [hj])))).1
omit [CompleteSpace H] in
lemma hilbertTrace_sum (b : HilbertBasis ι ℂ H) (s : Finset a) (A : a→H→L[ℂ]H)
    (hA : ∀ i∈s, HasFinitePositiveTrace b (A i)) :
    hilbertTrace b (∑ i∈s, A i)=∑ i∈s, hilbertTrace b (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hilbertTrace]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi,
      hilbertTrace_add b _ _ (hA i (by simp)).2 (finitePositiveTrace_sum b s A (fun j hj => hA j (by simp [hj]))).2,
      ih (fun j hj => hA j (by simp [hj]))]
namespace PositiveHilbertMeasure
variable {b : HilbertBasis ι ℂ H}

def familySum (s : Finset a) (W : a→PositiveHilbertMeasure T H b) : PositiveHilbertMeasure T H b where
  value A := ∑ i∈s, (W i).value A
  coeff x y := ∑ i∈s, (W i).coeff x y
  coeff_value x y A hA := by
    simp only [_root_.sum_apply, sum_apply, inner_sum]
    exact Finset.sum_congr rfl (fun i hi => (W i).coeff_value x y A hA)
  positive A hA := finitePositiveTrace_sum b s (fun i => (W i).value A) (fun i hi => (W i).positive A hA)
  traceMeasure := ∑ i∈s, (W i).traceMeasure
  traceFinite := inferInstance
  trace_value A hA := by
    rw [Measure.real,Measure.finsetSum_apply,ENNReal.toReal_sum (fun i hi => measure_ne_top (W i).traceMeasure A),
      hilbertTrace_sum b s _ (fun i hi => (W i).positive A hA)]
    exact Finset.sum_congr rfl (fun i hi => (W i).trace_value A hA)
lemma familySum_value (s : Finset a) (W : a→PositiveHilbertMeasure T H b) (A : Set T) :
    (familySum s W).value A=∑ i∈s, (W i).value A := rfl

def scale (W : PositiveHilbertMeasure T H b) (c : ℝ) (hc : 0≤c) : PositiveHilbertMeasure T H b where
  value A := (c : ℂ) • W.value A
  coeff x y := (c : ℂ) • W.coeff x y
  coeff_value x y A hA := by
    simp only [_root_.smul_apply,smul_eq_mul,inner_smul_right,W.coeff_value x y A hA]
  positive A hA := finitePositiveTrace_real_smul b c hc (W.positive A hA)
  traceMeasure := ENNReal.ofReal c • W.traceMeasure
  traceFinite := ⟨by
    simpa only [Measure.smul_apply,smul_eq_mul] using
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top W.traceMeasure Set.univ)⟩
  trace_value A hA := by
    rw [Measure.real,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc,
      hilbertTrace_real_smul,← W.trace_value A hA]
    rfl
lemma scale_value (W : PositiveHilbertMeasure T H b) (c : ℝ) (hc : 0≤c) (A : Set T) :
    (W.scale c hc).value A=(c : ℂ) • W.value A := rfl
end PositiveHilbertMeasure
lemma hilbertVariation_zero (b : HilbertBasis ι ℂ H) :
    hilbertVariation b (fun _ : Set T => (0 : H→L[ℂ]H))=0 := by
  simp [hilbertVariation,hilbertENorm]
lemma hilbertVariation_sum_le (b : HilbertBasis ι ℂ H) (s : Finset a) (F : a→Set T→H→L[ℂ]H)
    (hF : ∀ i∈s, ∀ A, MeasurableSet A → HermitianTraceClass b (F i A)) :
    hilbertVariation b (fun A => ∑ i∈s, F i A)≤∑ i∈s, hilbertVariation b (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,hilbertVariation_zero,le_refl]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    apply (hilbertVariation_add_le b _ _ (hF i (by simp))
      (fun A hA => hermitianTraceClass_sum b s (fun j => F j A) (fun j hj => hF j (by simp [hj]) A hA))).trans
    exact add_le_add le_rfl (ih (fun j hj => hF j (by simp [hj])))

end SecretKey

end

end OAI
