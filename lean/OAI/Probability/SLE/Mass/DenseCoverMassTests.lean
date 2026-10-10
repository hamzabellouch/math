import OAI.Probability.SLE.Gauge.DenseCoverAdaptedTests
import OAI.Probability.SLE.Geometry.FrontSuccessStopped
import OAI.Probability.SLE.Gauge.CoverEvents

namespace OAI

/-! Actual sausage tests at successive stopping times.  Their terminal
candidate implication is deterministic, whereas their failure calculation
uses only information observable at each test endpoint. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open FrontSuccessMeasurability

local instance denseMassPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance denseMassPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

def stoppedWholeSausageCharge (κ : ℝ) (f : C(ℝ≥0, ℂ))
    (τ : WithTop ℝ≥0) (v : ℝ) (D : Set ℂ) : ℝ≥0∞ :=
  wholeSausageCharge κ (stoppedAtPath f τ) v D

theorem stoppedWholeSausageCharge_le_whole
    (κ : ℝ) (f : C(ℝ≥0, ℂ)) (τ : WithTop ℝ≥0) (v : ℝ) (D : Set ℂ) :
    stoppedWholeSausageCharge κ f τ v D ≤ wholeSausageCharge κ f v D := by
  apply mul_le_mul' le_rfl
  apply measure_mono
  rintro z ⟨hz, t, ht⟩
  refine ⟨hz, (min τ (t : WithTop ℝ≥0)).untopA, ?_⟩
  simpa only [stoppedAtPath_apply] using ht

theorem stoppedWholeSausageCharge_finite
    (κ : ℝ) (f : C(ℝ≥0, ℂ)) (τ : ℝ≥0) (v : ℝ) (D : Set ℂ) :
    stoppedWholeSausageCharge κ f (τ : WithTop ℝ≥0) v D =
      segmentSausageCharge κ f 0 τ v D := by
  simp only [stoppedWholeSausageCharge, stoppedAtPath, WithTop.coe_ne_top, ite_false,
    WithTop.untopD_coe, segmentSausageCharge, wholeSausageCharge,
    sourceSausageSet_eq_clamped f 0 τ bot_le]

theorem stoppedWholeSausageCharge_measurable_at_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (γ : Ω → ℝ≥0 → ℂ) (ha : Adapted ℱ (fun t ω => γ ω t))
    (hc : ∀ ω, Continuous (γ ω))
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ) (κ v : ℝ) (D : Set ℂ) :
    Measurable[hτ.measurableSpace] (fun ω =>
      stoppedWholeSausageCharge κ (sourceTracePath γ hc ω) (τ ω) v D) :=
  (wholeSausageCharge_measurable κ v D).comp
    (stoppedAtPath_measurable ℱ γ ha hc τ hτ)

def clockStopFiltration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (τ : ℕ → Ω → WithTop ℝ≥0) (hτ : ∀ j, IsStoppingTime ℱ (τ j))
    (hmono : ∀ ω, Monotone (fun j => τ j ω)) : Filtration ℕ mΩ :=
  ⟨fun j => (hτ j).measurableSpace,
    fun _ _ hij => IsStoppingTime.measurableSpace_mono _ _ (fun ω => hmono ω hij),
    fun j => (hτ j).measurableSpace_le⟩

def stoppedMassTest
    {Ω : Type*} (κ v : ℝ) (f : Ω → C(ℝ≥0, ℂ))
    (τ : Ω → WithTop ℝ≥0) (D : Set ℂ) (b : ℝ) : Set Ω :=
  {ω | ENNReal.ofReal b ≤ stoppedWholeSausageCharge κ (f ω) (τ ω) v D}

theorem stoppedMassTest_measurable_at_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (γ : Ω → ℝ≥0 → ℂ) (ha : Adapted ℱ (fun t ω => γ ω t))
    (hc : ∀ ω, Continuous (γ ω))
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ) (κ v b : ℝ) (D : Set ℂ) :
    MeasurableSet[hτ.measurableSpace]
      (stoppedMassTest κ v (sourceTracePath γ hc) τ D b) :=
  measurableSet_le measurable_const
    (stoppedWholeSausageCharge_measurable_at_stop ℱ γ ha hc τ hτ κ v D)

/-- No terminal candidate forces failure of every earlier adapted test.
The terminal candidate is never put inside a finite change of measure. -/
theorem no_terminal_candidate_subset_stopped_failures
    {Ω : Type*} (κ v : ℝ) (f : Ω → C(ℝ≥0, ℂ))
    (τ : ℕ → Ω → WithTop ℝ≥0) (D : ℕ → Set ℂ) (b : ℕ → ℝ) (I : Finset ℕ) :
    {ω | ∀ j ∈ I, wholeSausageCharge κ (f ω) v (D j) < ENNReal.ofReal (b j)} ⊆
      ⋂ j ∈ I, (stoppedMassTest κ v f (τ (j + 1)) (D j) (b j))ᶜ := by
  intro ω hω
  apply mem_iInter₂.mpr
  intro j hj hsuccess
  exact (not_le_of_gt (hω j hj))
    (hsuccess.trans (stoppedWholeSausageCharge_le_whole κ (f ω) _ v (D j)))

/-- The actual successive stopped-sausage tests give the stretched
exponential missed-candidate bound under their finite stopped law. -/
theorem stoppedMassTests_cover_failure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 mΩ)
    (γ : Ω → ℝ≥0 → ℂ) (ha : Adapted ℱ (fun t ω => γ ω t))
    (hc : ∀ ω, Continuous (γ ω))
    (τ : ℕ → Ω → WithTop ℝ≥0) (hτ : ∀ j, IsStoppingTime ℱ (τ j))
    (hmono : ∀ ω, Monotone (fun j => τ j ω))
    (κ v : ℝ) (D : ℕ → Set ℂ) (b : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hstep : ∀ j (B : Set Ω), MeasurableSet[(hτ j).measurableSpace] B →
      ENNReal.ofReal (1 / Real.sqrt (n : ℝ)) * μ B ≤
        μ (B ∩ stoppedMassTest κ v (sourceTracePath γ hc) (τ (j + 1)) (D j) (b j))) :
    μ {ω | ∀ j ∈ coverTestWindow n,
      wholeSausageCharge κ (γ ω) v (D j) < ENNReal.ofReal (b j)} ≤
        ENNReal.ofReal (Real.exp (-Real.sqrt (n : ℝ) / 4)) := by
  let f := sourceTracePath γ hc
  let success := fun j => stoppedMassTest κ v f (τ (j + 1)) (D j) (b j)
  refine (measure_mono (no_terminal_candidate_subset_stopped_failures
    κ v f τ D b (coverTestWindow n))).trans ?_
  exact cover_window_failure_bound μ (clockStopFiltration ℱ τ hτ hmono) success
    (fun j => stoppedMassTest_measurable_at_stop ℱ γ ha hc (τ (j + 1)) (hτ (j + 1))
      κ v (b j) (D j)) n hn hstep

end SLEExactGauge

end

end OAI
