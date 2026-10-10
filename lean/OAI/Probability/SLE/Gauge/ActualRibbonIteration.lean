import OAI.Probability.SLE.Gauge.ActualRibbonPrefixBound
import OAI.Probability.SLE.Gauge.RibbonExperimentAssembly

namespace OAI

/-! Iteration along the actual global integer fronts. Previous successes
supply admissibility; no independence or deterministic completion bound is
required on failed samples. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates FirstFrontPassage Target

local instance ribbonIterationPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance ribbonIterationPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

def ribbonIntegerFront {Ω : Type*} (g : C(ℂ, ℝ)) (γ : Ω → ℝ≥0 → ℂ)
    (n : ℕ) : Ω → WithTop ℝ≥0 := ribbonFrontStop g γ ((n : ℝ) + 1)

lemma ribbonIntegerFront_monotone {Ω : Type*} (g : C(ℂ, ℝ)) (γ : Ω → ℝ≥0 → ℂ)
    (hc : ∀ ω, Continuous (γ ω)) (h0 : ∀ ω, g (γ ω 0) = 0) :
    Monotone (ribbonIntegerFront g γ) := by
  intro n k hnk ω
  exact firstFrontTime_mono_of_initial _ (g.continuous.comp (hc ω))
    (by change g (γ ω 0) ≤ (n : ℝ) + 1; rw [h0 ω]; positivity) (by exact_mod_cast Nat.add_le_add_right hnk 1)

def actualRibbonSuccess {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ)
    (g : C(ℂ, ℝ)) (P : ℂ → ℂ) (ε κ v c : ℝ) (n : ℕ) : Set Ω :=
  RibbonStepSuccess γ (ribbonIntegerFront g γ n) (ribbonIntegerFront g γ (n + 1))
    P ε κ v c (physicalMiddleRegion P closedRibbon ((n : ℝ) + 1) ε)

/-- Actual fronts turn the quantitative step estimate into a product
lower bound for the exact physical passage-and-mass events. -/
theorem actual_ribbon_successes_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ)
    (γ : Ω → ℝ≥0 → ℂ) (ha : Adapted ℱ (fun t ω => γ ω t))
    (hc : ∀ ω, Continuous (γ ω)) (g : C(ℂ, ℝ)) (hg0 : ∀ ω, g (γ ω 0) = 0)
    (P : ℂ → ℂ) (hemb : Topology.IsClosedEmbedding (fun z : closedRibbon => P z))
    (ε κ v c : ℝ) (q : ℝ≥0∞)
    (hstep : ∀ (n : ℕ) (A : Set Ω),
      MeasurableSet[(ribbonFrontStop_stopping ℱ g γ ha hc ((n : ℝ) + 1)).measurableSpace] A →
      A ⊆ GoodRibbonPrefix γ (ribbonIntegerFront g γ n) P ε →
        q * μ A ≤ μ (A ∩ actualRibbonSuccess γ g P ε κ v c n)) :
    ∀ N : ℕ, q ^ N * μ (GoodRibbonPrefix γ (ribbonIntegerFront g γ 0) P ε) ≤
      μ (GoodRibbonPrefix γ (ribbonIntegerFront g γ 0) P ε ∩
        ⋂ n ∈ Finset.range N, actualRibbonSuccess γ g P ε κ v c n) := by
  let τ := ribbonIntegerFront g γ
  have hτ (n : ℕ) : IsStoppingTime ℱ (τ n) :=
    ribbonFrontStop_stopping ℱ g γ ha hc ((n : ℝ) + 1)
  have hmono : Monotone τ := ribbonIntegerFront_monotone g γ hc hg0
  let 𝒢 : Filtration ℕ mΩ := ⟨fun n => (hτ n).measurableSpace,
    fun _ _ h => IsStoppingTime.measurableSpace_mono _ _ (hmono h),
    fun n => (hτ n).measurableSpace_le⟩
  let init := GoodRibbonPrefix γ (τ 0) P ε
  have hinit : MeasurableSet[𝒢 0] init :=
    goodRibbonPrefix_measurable ℱ γ ha hc (τ 0) (hτ 0) P hemb ε
  have hsuccess (n : ℕ) : MeasurableSet[𝒢 (n + 1)] (actualRibbonSuccess γ g P ε κ v c n) :=
    ribbonStepSuccess_measurable ℱ γ ha hc (τ n) (τ (n + 1)) (hτ n) (hτ (n + 1))
      (hmono (Nat.le_succ n)) P hemb ε κ v c _
  apply adapted_successes_lower_bound_on_previous μ 𝒢 init hinit _ hsuccess q
  intro n A hA hprev
  apply hstep n A hA
  intro ω hω
  have hωprev := hprev hω
  cases n with
  | zero => exact hωprev.1
  | succ n =>
    have hh := mem_iInter.mp (mem_iInter.mp hωprev.2 n) (Finset.mem_range.mpr (Nat.lt_succ_self n))
    exact hh.1

end SLEExactGauge

end

end OAI
