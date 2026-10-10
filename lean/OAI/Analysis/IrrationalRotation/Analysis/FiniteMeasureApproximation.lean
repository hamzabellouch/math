import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Tactic

namespace OAI

noncomputable section
open Filter MeasureTheory Set
open scoped Topology

namespace Invariant233.FiniteMeasureApproximation

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem tendsto_integral_of_uniform_approximation
    (μ : ℕ → Measure X) (ν : Measure X)
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν]
    (M : ℝ) (hM : 0 ≤ M) (hmass : ∀ n, (μ n).real univ ≤ M)
    (f : C(X, ℝ)) (g : ℕ → C(X, ℝ))
    (happrox : TendstoUniformly (fun k x => g k x) f atTop)
    (hconv : ∀ k, Tendsto (fun n => ∫ x, g k x ∂μ n) atTop (𝓝 (∫ x, g k x ∂ν))) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let C : ℝ := M + ν.real univ + 1
  have hν : 0 ≤ ν.real univ := ENNReal.toReal_nonneg
  have hC : 0 < C := by dsimp [C]; linarith
  let δ : ℝ := (ε / 3) / C
  have hδ : 0 < δ := div_pos (by positivity) hC
  have hδC : δ * C = ε / 3 := div_mul_cancel₀ _ (ne_of_gt hC)
  obtain ⟨k, hk⟩ := ((Metric.tendstoUniformly_iff.mp happrox) δ hδ).exists
  have herr (ρ : Measure X) [IsFiniteMeasure ρ] (hρ : ρ.real univ ≤ C) :
      dist (∫ x, f x ∂ρ) (∫ x, g k x ∂ρ) ≤ ε / 3 := by
    rw [dist_eq_norm, ← integral_sub
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((g k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    calc
      ‖∫ x, f x - g k x ∂ρ‖ ≤ δ * ρ.real univ := by
        apply norm_integral_le_of_norm_le_const
        filter_upwards with x
        simpa only [dist_eq_norm] using (hk x).le
      _ ≤ δ * C := mul_le_mul_of_nonneg_left hρ hδ.le
      _ = ε / 3 := hδC
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hconv k)) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have ha := herr (μ n) (by have := hmass n; dsimp [C]; linarith)
  have hb := hN n hn
  have hc := herr ν (by dsimp [C]; linarith)
  have htri := dist_triangle (∫ x, f x ∂μ n) (∫ x, g k x ∂μ n) (∫ x, f x ∂ν)
  have htri' := dist_triangle (∫ x, g k x ∂μ n) (∫ x, g k x ∂ν) (∫ x, f x ∂ν)
  rw [dist_comm (∫ x, g k x ∂ν) (∫ x, f x ∂ν)] at htri'
  linarith

end Invariant233.FiniteMeasureApproximation

end

end OAI
