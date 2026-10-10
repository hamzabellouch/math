import OAI.Probability.SLE.Geometry.ExtendedMarkedAngle
import OAI.Probability.SLE.Geometry.FiniteStoppedScalar

namespace OAI

/-! The full marked angle at a possibly infinite stopping time is
measurable in its stopped past, with value zero on the infinite event. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def extendedMarkedAngle {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (σ : Ω → WithTop ℝ≥0) (z : ℂ) (ω : Ω) : ℝ :=
  if σ ω=⊤ then 0 else
    (stoppedMarkedCenter κ B γ G (fun ω => (σ ω).untopD 0) z ω).arg

lemma stoppedMarkedCenter_time_congr {Ω : Type*}
    (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (σ τ : Ω → ℝ≥0) (z : ℂ) (ω : Ω) (h : σ ω=τ ω) :
    stoppedMarkedCenter κ B γ G σ z ω=stoppedMarkedCenter κ B γ G τ z ω := by
  classical
  exact congrArg (fun t => (if z∈survivingDomain (γ ω) t then G ω t z else 0)-
    ((Real.sqrt κ*B t ω:ℝ):ℂ)) h

lemma extendedMarkedAngle_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (σ : Ω → WithTop ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) σ)
    (z : ℂ) :
    Measurable[hσ.measurableSpace] (extendedMarkedAngle κ B γ G σ z) := by
  let X := fun n : ℕ => (finiteStopEvent σ n).indicator (fun ω =>
    (stoppedMarkedCenter κ B γ G (cutoffStop σ n) z ω).arg)
  have hX (n : ℕ) : Measurable[hσ.measurableSpace] (X n) := by
    have hcut := cutoffStop_stopping _ σ hσ (n:ℝ≥0)
    have hp := (source_stoppedMarkedCenter_measurable B hm hc κ γ G F hw
      (cutoffStop σ n) hcut z).carg
    exact (hp.mono (cutoffStop_past_le _ σ hσ n) le_rfl).indicator
      (finiteStopEvent_measurable _ σ hσ n)
  apply @measurable_of_tendsto_metrizable Ω ℝ hσ.measurableSpace _ _ _ _ X
    (extendedMarkedAngle κ B γ G σ z) hX
  apply tendsto_pi_nhds.mpr
  intro ω
  by_cases hs : σ ω=⊤
  · have he (n : ℕ) : X n ω=0 := by simp [X,finiteStopEvent,hs]
    simpa only [he,extendedMarkedAngle,hs,ite_true] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  · have hf : σ ω<⊤ := lt_top_iff_ne_top.mpr hs
    have hmem : ω∈⋃ n, finiteStopEvent σ n := by rw [iUnion_finiteStopEvent]; exact hf
    obtain ⟨n,hn⟩ := mem_iUnion.mp hmem
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n,cutoffStop_eventually_eq σ ω hf] with k hk he
    dsimp only [X]
    rw [indicator_of_mem (finiteStopEvent_mono σ hk hn),
      stoppedMarkedCenter_time_congr κ B γ G (cutoffStop σ k)
        (fun ω => (σ ω).untopD 0) z ω he]
    exact ite_eq_right hs

end SLEExactGauge

end

end OAI
