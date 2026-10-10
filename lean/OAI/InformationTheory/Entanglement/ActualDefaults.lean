import OAI.InformationTheory.Entanglement.HilbertVectorMeasure
import OAI.InformationTheory.Entanglement.HilbertRecordMap
import OAI.InformationTheory.Entanglement.HilbertCoarsegrain

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder MeasureTheory
open ContinuousLinearMap MeasureTheory Filter
namespace SecretKey
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
namespace PositiveHilbertMeasure
variable {b : HilbertBasis ι ℂ H} (W : PositiveHilbertMeasure X H b)

lemma value_eq_zero_of_trace_null {s : Set X} (hs : MeasurableSet s)
    (hz : W.traceMeasure s=0) : W.value s=0 := by
  have hn : W.traceValue s=0 := by
    apply norm_eq_zero.mp
    rw [W.traceValue_norm hs,Measure.real,hz,ENNReal.toReal_zero]
  rw [← W.traceValue_operator hs,hn]
  rfl
lemma coeff_eq_zero_of_trace_null (x y : H) {s : Set X} (hs : MeasurableSet s)
    (hz : W.traceMeasure s=0) : W.coeff x y s=0 := by
  rw [W.coeff_value x y s hs,W.value_eq_zero_of_trace_null hs hz]
  simp

lemma value_eq_of_ae_set {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (he : s =ᵐ[W.traceMeasure] t) : W.value s=W.value t := by
  have hzst : W.traceMeasure (s \ t)=0 := by
    apply measure_mono_null (fun x hx => ?_) (ae_iff.mp he)
    change ¬ ((x∈s)=(x∈t))
    intro h
    exact hx.2 (Eq.mp h hx.1)
  have hzts : W.traceMeasure (t \ s)=0 := by
    apply measure_mono_null (fun x hx => ?_) (ae_iff.mp he)
    change ¬ ((x∈s)=(x∈t))
    intro h
    exact hx.2 (Eq.mpr h hx.1)
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [← W.coeff_value x y s hs,← W.coeff_value x y t ht]
  have h := VectorMeasure.of_sdiff_of_sdiff_eq_zero hs ht
    (W.coeff_eq_zero_of_trace_null x y (ht.diff hs) hzts)
  rw [W.coeff_eq_zero_of_trace_null x y (hs.diff ht) hzst,zero_add] at h
  exact h.symm

lemma mapRecord_value_congr_ae (f g : X→Y) (hf : Measurable f) (hg : Measurable g)
    (he : f =ᵐ[W.traceMeasure] g) (s : Set Y) (hs : MeasurableSet s) :
    (W.mapRecord f hf).value s=(W.mapRecord g hg).value s := by
  apply W.value_eq_of_ae_set (hf hs) (hg hs)
  filter_upwards [he] with z hz
  change (f z∈s)=(g z∈s)
  rw [hz]
end PositiveHilbertMeasure
local instance : MeasurableSpace (Option (Fin 2)) := ⊤
local instance : MeasurableSingletonClass (Option (Fin 2)) := ⟨fun _ => trivial⟩

theorem actual_completion_removes_defaults
    {T : Type*} [MeasurableSpace T] {b : HilbertBasis ι ℂ H}
    (W : PositiveHilbertMeasure X H b)
    (t : X→T) (ha hb : X→Option (Fin 2)) (a c : X→Fin 2)
    (ht : Measurable t) (hha : Measurable ha) (hhb : Measurable hb)
    (haM : Measurable a) (hcM : Measurable c)
    (hcompleteA : ha =ᵐ[W.traceMeasure] (fun x => some (a x)))
    (hcompleteB : hb =ᵐ[W.traceMeasure] (fun x => some (c x)))
    (s : Set (T×(Fin 2×Fin 2))) (hs : MeasurableSet s) :
    W.value ((fun x => (t x,(abortToZero (ha x),abortToZero (hb x)))) ⁻¹' s)=
      W.value ((fun x => (t x,(a x,c x))) ⁻¹' s) := by
  have hD : Measurable abortToZero := measurable_of_countable abortToZero
  apply W.value_eq_of_ae_set
    ((ht.prodMk ((hD.comp hha).prodMk (hD.comp hhb))) hs)
    ((ht.prodMk (haM.prodMk hcM)) hs)
  filter_upwards [hcompleteA,hcompleteB] with x hA hB
  change ((t x,(abortToZero (ha x),abortToZero (hb x)))∈s)=((t x,(a x,c x))∈s)
  rw [hA,hB,abortToZero_some,abortToZero_some]

end SecretKey

end

end OAI
