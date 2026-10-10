import OAI.Probability.SLE.Stochastic.ProgressiveStoppedTime
import OAI.Probability.SLE.Geometry.ExtendedStopLocalization

namespace OAI

/-! A progressive scalar evaluated at a possibly infinite stop, with zero
on the infinite event, is measurable in the original stopped past. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge

def finiteStoppedScalar {Ω : Type*} (A : ℝ≥0 → Ω → ℝ)
    (S : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ :=
  if S ω=⊤ then 0 else A ((S ω).untopD 0) ω

lemma finiteStoppedScalar_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (A : ℝ≥0 → Ω → ℝ) (hA : IsProgressive ℱ A)
    (S : Ω → WithTop ℝ≥0) (hS : IsStoppingTime ℱ S) :
    Measurable[hS.measurableSpace] (finiteStoppedScalar A S) := by
  let X := fun n : ℕ => (finiteStopEvent S n).indicator (fun ω => A (cutoffStop S n ω) ω)
  have hm (n : ℕ) : Measurable[hS.measurableSpace] (X n) := by
    have hh := _root_.OAI.MeasureTheory.IsProgressive.stopped_time_measurable hA (cutoffStop S n) (cutoffStop_stopping ℱ S hS n)
    exact (hh.mono (cutoffStop_past_le ℱ S hS n) le_rfl).indicator
      (finiteStopEvent_measurable ℱ S hS n)
  apply @measurable_of_tendsto_metrizable Ω ℝ hS.measurableSpace _ _ _ _ X (finiteStoppedScalar A S) hm
  apply tendsto_pi_nhds.mpr
  intro ω
  by_cases hs : S ω=⊤
  · have he (n : ℕ) : X n ω=0 := by simp [X,finiteStopEvent,hs]
    simpa only [he,finiteStoppedScalar,hs,ite_true] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  · have hf : S ω<⊤ := lt_top_iff_ne_top.mpr hs
    have hmemb : ω∈⋃ n, finiteStopEvent S n := by rw [iUnion_finiteStopEvent]; exact hf
    obtain ⟨n,hn⟩ := mem_iUnion.mp hmemb
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n,cutoffStop_eventually_eq S ω hf] with k hk he
    simp only [finiteStoppedScalar,hs,ite_false,X,
      indicator_of_mem (finiteStopEvent_mono S hk hn),he]

lemma integral_eq_of_stopped_events
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P Q : Measure Ω) (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (he : ∀ E, MeasurableSet[m] E → P E=Q E)
    (X : Ω → ℝ) (hX : Measurable[m] X) :
    (∫ ω, X ω ∂P)=(∫ ω, X ω ∂Q) := by
  have htrim : P.trim hm=Q.trim hm := by
    ext E hE
    rw [trim_measurableSet_eq hm hE,trim_measurableSet_eq hm hE]
    exact he E hE
  calc
    (∫ ω, X ω ∂P) = (∫ ω, X ω ∂P.trim hm) :=
      integral_trim hm hX.stronglyMeasurable
    _ = (∫ ω, X ω ∂Q.trim hm) := by rw [htrim]
    _ = _ := (integral_trim hm hX.stronglyMeasurable).symm

lemma lintegral_eq_of_stopped_events
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P Q : Measure Ω) (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (he : ∀ E, MeasurableSet[m] E → P E=Q E)
    (X : Ω → ℝ≥0∞) (hX : Measurable[m] X) :
    (∫⁻ ω, X ω ∂P)=(∫⁻ ω, X ω ∂Q) := by
  have htrim : P.trim hm=Q.trim hm := by
    ext E hE
    rw [trim_measurableSet_eq hm hE,trim_measurableSet_eq hm hE]
    exact he E hE
  calc
    (∫⁻ ω, X ω ∂P) = (∫⁻ ω, X ω ∂P.trim hm) := (lintegral_trim hm hX).symm
    _ = (∫⁻ ω, X ω ∂Q.trim hm) := by rw [htrim]
    _ = _ := lintegral_trim hm hX

end SLEExactGauge

end

end OAI
