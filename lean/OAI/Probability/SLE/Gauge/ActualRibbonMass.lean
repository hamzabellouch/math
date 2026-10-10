import OAI.Probability.SLE.Gauge.PublishedRibbonIteration

namespace OAI

/-! Charge selected actual successive-front windows to a single sausage,
retaining the successful terminal prefix for clearance and density transfer. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates

lemma actual_successes_terminal_prefix
    {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ) (g : C(ℂ, ℝ)) (P : ℂ → ℂ)
    (ε κ v c : ℝ) (N : ℕ) (ω : Ω)
    (hω : ω ∈ GoodRibbonPrefix γ (ribbonIntegerFront g γ 0) P ε ∩
      ⋂ n ∈ Finset.range N, actualRibbonSuccess γ g P ε κ v c n) :
    ω ∈ GoodRibbonPrefix γ (ribbonIntegerFront g γ N) P ε := by
  cases N with
  | zero => exact hω.1
  | succ N =>
    exact (mem_iInter.mp (mem_iInter.mp hω.2 N) (Finset.mem_range.mpr (Nat.lt_succ_self N))).1

/-- Only selected middle strips are charged. The trace windows are the
original actual fronts, including their exact starting and ending times. -/
theorem actual_successes_force_whole_mass
    {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ) (g : C(ℂ, ℝ)) (P : ℂ → ℂ)
    (hplanar : PublishedPlanarDiskOpenness) (hP : ContinuousOn P closedRibbon)
    (hi : InjOn P closedRibbon) (ε κ v c : ℝ) (hε : ε ≤ 1)
    (N : ℕ) (I : Finset ℕ) (hI : ∀ i ∈ I, 0 < i ∧ i ≤ N) (D : Set ℂ)
    (hregions : ∀ i ∈ I, physicalMiddleRegion P closedRibbon i ε ⊆ D)
    (ω : Ω) (hω : ω ∈ GoodRibbonPrefix γ (ribbonIntegerFront g γ 0) P ε ∩
      ⋂ n ∈ Finset.range N, actualRibbonSuccess γ g P ε κ v c n) :
    ω ∈ GoodRibbonPrefix γ (ribbonIntegerFront g γ N) P ε ∧
      (I.card : ℝ≥0∞) * ENNReal.ofReal c ≤ wholeSausageCharge κ (γ ω) v D := by
  refine ⟨actual_successes_terminal_prefix γ g P ε κ v c N ω hω, ?_⟩
  apply whole_sausage_charge_from_ribbon_steps hplanar P hP hi hε I κ (γ ω)
    (fun i => (ribbonIntegerFront g γ (i - 1) ω).untopD 0)
    (fun i => (ribbonIntegerFront g γ i ω).untopD 0) v c D hregions
  intro i hiI
  obtain ⟨hi0, hiN⟩ := hI i hiI
  have hsub : i - 1 + 1 = i := Nat.sub_add_cancel hi0
  have hreal : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast hsub
  have hn : i - 1 < N := by omega
  have hs := (mem_iInter.mp (mem_iInter.mp hω.2 (i - 1)) (Finset.mem_range.mpr hn)).2
  simpa only [actualRibbonSuccess, RibbonStepSuccess, mem_inter_iff, mem_ofPred_eq,
    hsub, hreal] using hs

end SLEExactGauge

end

end OAI
