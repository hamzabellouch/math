import OAI.InformationTheory.Entanglement.ReferenceFilter

namespace OAI

noncomputable section
open scoped MeasureTheory BigOperators ComplexOrder MatrixOrder
open MeasureTheory Matrix Filter
namespace SecretKey
open ChannelCompletion
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
variable {n : Type} [Fintype n]
namespace PositiveMatrixMeasure
@[ext] lemma ext_entry_default {W V : PositiveMatrixMeasure Ω n} (h : W.entry=V.entry) : W=V := by
  cases W
  cases V
  cases h
  rfl
lemma value_zero_of_trace_zero (W : PositiveMatrixMeasure Ω n) {s : Set Ω}
    (hs : MeasurableSet s) (h0 : (Matrix.trace (W.value s)).re=0) : W.value s=0 := by
  apply (W.positive s hs).trace_eq_zero_iff.mp
  apply Complex.ext
  · exact h0
  · exact (Complex.nonneg_iff.mp (W.positive s hs).trace_nonneg).2.symm
lemma traceMeasure_eq_zero_iff (W : PositiveMatrixMeasure Ω n) {s : Set Ω}
    (hs : MeasurableSet s) : W.traceMeasure s=0 ↔ (Matrix.trace (W.value s)).re=0 := by
  rw [← W.traceMeasure_real hs,measureReal_def,ENNReal.toReal_eq_zero_iff]
  simp only [measure_ne_top,or_false]

lemma subevent_zero_of_trace_zero (W : PositiveMatrixMeasure Ω n) {N s : Set Ω}
    (hN : MeasurableSet N) (h0 : (Matrix.trace (W.value N)).re=0)
    (hs : MeasurableSet s) (hsN : s⊆N) : W.value s=0 := by
  apply W.value_zero_of_trace_zero hs
  apply (W.traceMeasure_eq_zero_iff hs).mp
  exact measure_mono_null hsN ((W.traceMeasure_eq_zero_iff hN).mpr h0)

def map (W : PositiveMatrixMeasure Ω n) (f : Ω → T) (hf : Measurable f) :
    PositiveMatrixMeasure T n where
  entry i j := (W.entry i j).map f
  positive s hs := by
    simpa only [VectorMeasure.map_apply _ hf hs] using W.positive (f⁻¹' s) (hf hs)
lemma map_value (W : PositiveMatrixMeasure Ω n) (f : Ω → T) (hf : Measurable f)
    {s : Set T} (hs : MeasurableSet s) : (W.map f hf).value s=W.value (f⁻¹' s) := by
  ext i j
  exact VectorMeasure.map_apply _ hf hs
lemma map_congr_trace_ae (W : PositiveMatrixMeasure Ω n) (f g : Ω → T)
    (hf : Measurable f) (hg : Measurable g) (hfg : f=ᵐ[W.traceMeasure]g) :
    W.map f hf=W.map g hg := by
  apply ext_entry_default
  ext i j s hs
  change ((W.entry i j).map f) s=((W.entry i j).map g) s
  rw [VectorMeasure.map_apply _ hf hs,VectorMeasure.map_apply _ hg hs]
  change W.value (f⁻¹' s) i j=W.value (g⁻¹' s) i j
  rw [    ← W.positiveDensity_setIntegral Measure.AbsolutelyContinuous.rfl (hf hs) i j,
    ← W.positiveDensity_setIntegral Measure.AbsolutelyContinuous.rfl (hg hs) i j]
  apply setIntegral_congr_set
  filter_upwards [hfg] with x hx
  exact congrArg (fun y => y ∈ s) hx

theorem default_output_unchanged (W : PositiveMatrixMeasure Ω n)
    (N : Set Ω) (hN : MeasurableSet N) (h0 : (Matrix.trace (W.value N)).re=0)
    (f g : Ω → T) (hf : Measurable f) (hg : Measurable g)
    (heq : ∀ x, x∉N → f x=g x) : W.map f hf=W.map g hg := by
  apply W.map_congr_trace_ae f g hf hg
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp ((W.traceMeasure_eq_zero_iff hN).mpr h0)] with x hx
  exact heq x hx
end PositiveMatrixMeasure

end SecretKey

end

end OAI
