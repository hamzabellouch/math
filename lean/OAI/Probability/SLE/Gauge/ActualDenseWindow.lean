import OAI.Probability.SLE.Gauge.ActualDenseConditional
import OAI.Probability.SLE.Gauge.WindowDenseTests
import OAI.Probability.SLE.Gauge.CoverRadiusLevels

namespace OAI

/-! Repeated actual dense tests on the retained scale window. All tests
are evaluated under one later finite centered law. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance actualWindowPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance actualWindowPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

def actualDenseScaleTest {Ω : Type*} (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ)
    (hc : ∀ ω, Continuous (γ ω)) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (z : ℂ) (T q b v : ℝ) (N j : ℕ) : Set Ω :=
  stoppedMassTest κ v (sourceTracePath γ hc)
    (fun ω => radiusLevelTime (γ ω) (G ω) z (coverLogLevel z T j + 1 + q))
    (closedBall z (Real.exp (-1) * coverRadius T j))
    (b * (Real.exp (-1) * coverRadius T j) ^ dimension κ * (N : ℝ) ^ codimension κ)

def actualDenseWindowFailure {Ω : Type*} (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ)
    (hc : ∀ ω, Continuous (γ ω)) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (z : ℂ) (T q b v : ℝ) (N n : ℕ) : Set Ω :=
  ⋂ j ∈ coverTestWindow n, (actualDenseScaleTest κ γ hc G z T q b v N j)ᶜ

lemma coverLogLevel_next_gap (z : ℂ) (T : ℝ) (j : ℕ)
    (hj : coverLogLevel z T j = Real.log (2 * z.im) + T * (j : ℝ)) :
    coverLogLevel z T j + T ≤ coverLogLevel z T (j + 1) := by
  rw [hj]
  apply le_trans _ (le_max_right _ _)
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

theorem actual_dense_window_failure_bound
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (T q b v C V : ℝ)
    (hT : 0 ≤ T) (hq : 0 ≤ q) (hgap : 1 + q ≤ T) (hV : 0 ≤ V)
    (N n : ℕ) (hn : 1 ≤ n)
    (hlevel : ∀ j ∈ coverTestWindow n,
      coverLogLevel z T j = Real.log (2 * z.im) + T * (j : ℝ))
    (hprob : 1 / Real.sqrt (n : ℝ) ≤ (1 / 2) * Real.exp (-C * (N : ℝ) ^ 2))
    (hdense : ∀ j ∈ coverTestWindow n, ∀ A : Set Ω,
      MeasurableSet[(actual_radiusLevelTime_stopping hB
        (fun _t => hBm.comp (measurable_const.prodMk measurable_id)) hBm hc hB0
        κ hκ hκ8 γ G F hw z hz (coverLogLevel z T j) (coverLogLevel_nonneg _ _ _)).measurableSpace] A →
      ENNReal.ofReal ((1 / 2) * Real.exp (-C * (N : ℝ) ^ 2)) *
        finiteCenteredLaw P κ B γ G z V A ≤
      finiteCenteredLaw P κ B γ G z V
        (A ∩ actualDenseScaleTest κ γ (fun ω => (hw ω).1) G z T q b v N j)) :
    finiteCenteredLaw P κ B γ G z V
      (actualDenseWindowFailure κ γ (fun ω => (hw ω).1) G z T q b v N n) ≤
      ENNReal.ofReal (Real.exp (-Real.sqrt (n : ℝ) / 4)) := by
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let ℱ := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let τ (j : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
    radiusLevelTime (γ ω) (G ω) z (coverLogLevel z T j)
  have hτ (j : ℕ) : IsStoppingTime ℱ (τ j) :=
    actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz _
      (coverLogLevel_nonneg _ _ _)
  have hmono (ω : Ω) : Monotone (fun j => τ j ω) := by
    intro i j hij
    exact radiusLevelTime_mono ((hc ω).const_mul _) (hw ω) z
      (coverLogLevel_nonneg _ _ _) (coverLogLevel_monotone z hT hij)
  let ℱc := clockStopFiltration ℱ τ hτ hmono
  have hγa : Adapted ℱ (fun t ω => γ ω t) := by
    apply capacity_trace_adapted _ (fun t ω => Real.sqrt κ * B t ω) _ _ γ G F hw
    · intro t
      exact measurable_const.mul
        ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)) t).measurable
    · intro ω
      exact (hc ω).const_mul _
  let := finiteCenteredLaw_probability hB κ hκ hκ8 γ G F (Eventually.of_forall hw) z hz V hV
  apply cover_window_failure_bound_on_window (finiteCenteredLaw P κ B γ G z V) ℱc
    (actualDenseScaleTest κ γ (fun ω => (hw ω).1) G z T q b v N) n hn
  · intro j hj
    have hend : coverLogLevel z T j + 1 + q ≤ coverLogLevel z T (j + 1) :=
      (by linarith : coverLogLevel z T j + 1 + q ≤ coverLogLevel z T j + T).trans
        (coverLogLevel_next_gap z T j (hlevel j hj))
    have hstop := actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8 γ G F hw
      z hz (coverLogLevel z T j + 1 + q) (by linarith [coverLogLevel_nonneg z T j])
    exact (actual_radiusLevelTime_past_mono hB hm hBm hc hB0 κ hκ hκ8 γ G F hw
      z hz _ _ (by linarith [coverLogLevel_nonneg z T j]) hend)
      _ (stoppedMassTest_measurable_at_stop ℱ γ hγa (fun ω => (hw ω).1)
        _ hstop κ v _ _)
  · intro j hj A hA
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hprob) le_rfl).trans (hdense j hj A hA)

theorem actual_dense_window_failure_measurable_at_end
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (T q b v : ℝ)
    (hT : 0 ≤ T) (hq : 0 ≤ q) (hgap : 1 + q ≤ T) (N n : ℕ)
    (hlevel : ∀ j ∈ coverTestWindow n,
      coverLogLevel z T j = Real.log (2 * z.im) + T * (j : ℝ)) :
    MeasurableSet[(actual_radiusLevelTime_stopping hB
      (fun _t => hBm.comp (measurable_const.prodMk measurable_id)) hBm hc hB0
      κ hκ hκ8 γ G F hw z hz (coverLogLevel z T (2 * n / 3 + 1))
      (coverLogLevel_nonneg _ _ _)).measurableSpace]
      (actualDenseWindowFailure κ γ (fun ω => (hw ω).1) G z T q b v N n) := by
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let ℱ := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hγa : Adapted ℱ (fun t ω => γ ω t) := by
    apply capacity_trace_adapted _ (fun t ω => Real.sqrt κ * B t ω) _ _ γ G F hw
    · intro t
      exact measurable_const.mul
        ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)) t).measurable
    · intro ω
      exact (hc ω).const_mul _
  apply MeasurableSet.biInter (coverTestWindow n).countable_toSet
  intro j hj
  apply MeasurableSet.compl
  have hend : coverLogLevel z T j + 1 + q ≤ coverLogLevel z T (2 * n / 3 + 1) := by
    have hj' : j + 1 ≤ 2 * n / 3 + 1 := Nat.add_le_add_right (Finset.mem_Icc.mp hj).2 1
    exact (by linarith : coverLogLevel z T j + 1 + q ≤ coverLogLevel z T j + T).trans
      ((coverLogLevel_next_gap z T j (hlevel j hj)).trans (coverLogLevel_monotone z hT hj'))
  have hstop := actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8 γ G F hw
    z hz (coverLogLevel z T j + 1 + q) (by linarith [coverLogLevel_nonneg z T j])
  exact (actual_radiusLevelTime_past_mono hB hm hBm hc hB0 κ hκ hκ8 γ G F hw
    z hz _ _ (by linarith [coverLogLevel_nonneg z T j]) hend)
    _ (stoppedMassTest_measurable_at_stop ℱ γ hγa (fun ω => (hw ω).1)
      _ hstop κ v _ _)

end SLEExactGauge

end

end OAI
