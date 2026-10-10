import OAI.Probability.FreeIsing.Brownian.IntegralProcess

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal
namespace Problem367.RandomStoppedSimpleIntegral

variable {Ω I : Type*} [LinearOrder I] [Nonempty I]

theorem stoppedProcess_min (B : I → Ω → ℝ) (τ : Ω → WithTop I) (a t : I) (ω : Ω) :
    stoppedProcess B τ (min t a) ω =
      B (min (min (t : WithTop I) (τ ω)).untopA a) ω := by
  rcases eq_or_ne (τ ω) ⊤ with hτ | hτ
  · simp only [stoppedProcess, hτ, min_eq_left le_top]
    rfl
  · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hτ
    simp only [stoppedProcess, ← hs, ← WithTop.coe_min]
    change B (min (min t a) s) ω = B (min (min t s) a) ω
    rw [min_right_comm t a s]

theorem stopped_intervalSum (B H : I → Ω → ℝ) (τ : Ω → WithTop I)
    {a b : I} (hab : a ≤ b) (t : I) (ω : Ω) :
    stoppedProcess (StoppedSimpleIntegral.intervalSum B (H a) a b) τ t ω =
      StoppedSimpleIntegral.intervalSum (stoppedProcess B τ)
        (stoppedProcess H τ a) a b t ω := by
  rw [StoppedSimpleIntegral.intervalSum, stoppedProcess_min, stoppedProcess_min]
  change H a ω * (B (min (min (t : WithTop I) (τ ω)).untopA b) ω -
    B (min (min (t : WithTop I) (τ ω)).untopA a) ω) = _
  by_cases ha : (a : WithTop I) ≤ τ ω
  · rw [stoppedProcess_eq_of_le ha]
  · have hτa : τ ω ≤ (a : WithTop I) := le_of_not_ge ha
    have hcap : (min (t : WithTop I) (τ ω)).untopA ≤ a := by
      exact WithTop.untopA_le ((min_le_right _ _).trans hτa)
    rw [min_eq_left hcap, min_eq_left (hcap.trans hab), sub_self, mul_zero, mul_zero]

theorem stopped_intervalSum_integrator (B : I → Ω → ℝ) (H : Ω → ℝ)
    (τ : Ω → WithTop I) (a b t : I) (ω : Ω) :
    stoppedProcess (StoppedSimpleIntegral.intervalSum B H a b) τ t ω =
      StoppedSimpleIntegral.intervalSum (stoppedProcess B τ) H a b t ω := by
  rw [StoppedSimpleIntegral.intervalSum, stoppedProcess_min, stoppedProcess_min]
  rfl

theorem stopped_finite_intervalSum {J : Type*} (s : Finset J)
    (B : I → Ω → ℝ) (H : J → Ω → ℝ) (a b : J → I) (τ : Ω → WithTop I) :
    stoppedProcess (fun t ω => ∑ i ∈ s,
      StoppedSimpleIntegral.intervalSum B (H i) (a i) (b i) t ω) τ =
    fun t ω => ∑ i ∈ s,
      StoppedSimpleIntegral.intervalSum (stoppedProcess B τ) (H i) (a i) (b i) t ω := by
  funext t ω
  change (∑ i ∈ s, stoppedProcess
    (StoppedSimpleIntegral.intervalSum B (H i) (a i) (b i)) τ t ω) = _
  exact Finset.sum_congr rfl fun i hi =>
    stopped_intervalSum_integrator B (H i) τ (a i) (b i) t ω

theorem stopped_uniformSum (B H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (n : ℕ) (τ : Ω → WithTop ℝ≥0) :
    stoppedProcess (BrownianIntegralProcess.stoppedUniformSum B H T n) τ =
      BrownianIntegralProcess.stoppedUniformSum
        (stoppedProcess B τ) (stoppedProcess H τ) T n := by
  funext t ω
  change (∑ i ∈ Finset.range n, stoppedProcess
    (StoppedSimpleIntegral.intervalSum B (H (BrownianGrid.uniformGrid T n i))
      (BrownianGrid.uniformGrid T n i) (BrownianGrid.uniformGrid T n (i + 1)))
    τ t ω) = _
  exact Finset.sum_congr rfl fun i hi => stopped_intervalSum B H τ
    (BrownianGrid.uniformGrid_mono T n (Nat.le_succ i)) t ω

end Problem367.RandomStoppedSimpleIntegral

end

end OAI
