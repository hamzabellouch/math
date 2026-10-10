import OAI.InformationTheory.Entanglement.HilbertLawDistance
import OAI.InformationTheory.Entanglement.HilbertTraceDifference

namespace OAI

noncomputable section
open scoped BigOperators ENNReal MeasureTheory InnerProductSpace ComplexOrder
open MeasureTheory ContinuousLinearMap
namespace SecretKey
variable {T : Type*} [MeasurableSpace T]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}
lemma hilbertDifference_enorm_le (b : HilbertBasis ι ℂ H)
    {A B : H →L[ℂ] H} (hA : HasFinitePositiveTrace b A) (hB : HasFinitePositiveTrace b B) :
    hilbertENorm b (A-B)≤ENNReal.ofReal (hilbertTrace b A)+ENNReal.ofReal (hilbertTrace b B) := by
  obtain ⟨ht,hb⟩ := positive_difference_traceClass b hA hB
  rw [hilbertENorm_eq b ht.2]
  apply (ENNReal.ofReal_le_ofReal hb).trans
  exact ENNReal.ofReal_add_le
lemma hilbertVariation_difference_le (b : HilbertBasis ι ℂ H)
    (W V : PositiveHilbertMeasure T H b) :
    hilbertVariation b (fun s => W.value s-V.value s)≤
      W.traceMeasure Set.univ+V.traceMeasure Set.univ := by
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  apply iSup_le
  intro hd
  have he (s : Set T) (hs : MeasurableSet s) :
      hilbertENorm b (W.value s-V.value s)≤W.traceMeasure s+V.traceMeasure s := by
    have h := hilbertDifference_enorm_le b (W.positive s hs) (V.positive s hs)
    rw [← W.trace_value s hs,← V.trace_value s hs,
      Measure.real,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
    exact h
  calc
    _ ≤ ∑ s∈P, (W.traceMeasure s+V.traceMeasure s) := Finset.sum_le_sum (fun s hs => he s (hP s hs))
    _ = (∑ s∈P, W.traceMeasure s)+(∑ s∈P, V.traceMeasure s) := Finset.sum_add_distrib
    _ ≤ W.traceMeasure Set.univ+V.traceMeasure Set.univ := add_le_add
      (sum_measure_le_measure_univ (fun s hs => (hP s hs).nullMeasurableSet) hd.aedisjoint)
      (sum_measure_le_measure_univ (fun s hs => (hP s hs).nullMeasurableSet) hd.aedisjoint)
lemma hilbertVariation_difference_ne_top (b : HilbertBasis ι ℂ H)
    (W V : PositiveHilbertMeasure T H b) :
    hilbertVariation b (fun s => W.value s-V.value s)≠⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,measure_ne_top _ _⟩)
    (hilbertVariation_difference_le b W V)

lemma hilbert_event_difference_norm (b : HilbertBasis ι ℂ H)
    (W V : PositiveHilbertMeasure T H b) {s : Set T} (hs : MeasurableSet s) :
    HermitianTraceClass b (W.value s-V.value s) ∧
      hilbertENorm b (W.value s-V.value s)=ENNReal.ofReal (hilbertTraceNorm b (W.value s-V.value s)) := by
  have ht := (positive_difference_traceClass b (W.positive s hs) (V.positive s hs)).1
  exact ⟨ht,hilbertENorm_eq b ht.2⟩
lemma hilbertVariation_le_measure (b : HilbertBasis ι ℂ H)
    (F : Set T → H →L[ℂ] H) (μ : Measure T)
    (h : ∀ s, MeasurableSet s → hilbertENorm b (F s)≤μ s) :
    hilbertVariation b F≤μ Set.univ := by
  apply iSup_le
  intro P
  apply iSup_le
  intro hm
  apply iSup_le
  intro hd
  exact (Finset.sum_le_sum (fun s hs => h s (hm s hs))).trans
    (sum_measure_le_measure_univ (fun s hs => (hm s hs).nullMeasurableSet) hd.aedisjoint)
lemma hilbertCQDistance_ne_top (b : HilbertBasis ι ℂ H)
    (W : Fin 2 → Fin 2 → PositiveHilbertMeasure T H b)
    (σ : PositiveHilbertMeasure T H b) : hilbertCQDistance b W σ≠⊤ := by
  have hb (i j : Fin 2) : hilbertVariation b
      (fun s => (W i j).value s-hilbertIdeal σ.value i j s)≤
        ((W i j).traceMeasure+σ.traceMeasure) Set.univ := by
    apply hilbertVariation_le_measure
    intro s hs
    have hn : 0≤hilbertTrace b (σ.value s) := by
      rw [← σ.trace_value s hs]
      exact measureReal_nonneg
    have hi : hilbertTrace b (hilbertIdeal σ.value i j s)≤hilbertTrace b (σ.value s) := by
      unfold hilbertIdeal
      split_ifs
      · rw [hilbertTrace_real_smul]; nlinarith
      · simpa only [hilbertTrace,zero_apply,inner_zero_right,Complex.zero_re,tsum_zero] using hn
    have he := hilbertDifference_enorm_le b ((W i j).positive s hs) (hilbertIdeal_positive b σ i j hs)
    apply he.trans
    rw [Measure.add_apply,← (W i j).trace_value s hs]
    apply add_le_add
    · exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).le
    · apply (ENNReal.ofReal_le_ofReal hi).trans
      rw [← σ.trace_value s hs]
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).le
  unfold hilbertCQDistance
  apply ENNReal.sum_ne_top.mpr
  intro i hi
  apply ENNReal.sum_ne_top.mpr
  intro j hj
  exact ne_top_of_le_ne_top (measure_ne_top _ _) (hb i j)

end SecretKey

end

end OAI
