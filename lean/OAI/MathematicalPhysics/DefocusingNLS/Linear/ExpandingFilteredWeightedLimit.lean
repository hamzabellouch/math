import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFilteredWeakLimit
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.LocalWeightedCompact

namespace OAI

/-! # The weighted physical L² limit of actual filtered derivatives -/

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem tendsto_expandingSmoothDerivative_weightedL2 (a k M S : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hS : 0 < S)
    (N : ℕ) (j : Fin N → Fin 12) (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (hlocal : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
      ‖expandingTorusFunction a k (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y))‖ < ε)
    (V : E → ℂ) (hV : MemLp V 2 volume) :
    Tendsto (fun n => ∫ y : E, ‖V y *
      expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n)
        (expandingSmoothDerivative (L n) S hS N j (f n)) y‖ ^ 2) atTop (𝓝 0) := by
  let u := fun n => expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n)
    (expandingSmoothDerivative (L n) S hS N j (f n))
  let D := expandingEmbeddingBound a k * (∫ z : E, ‖smoothDerivativeKernel S hS N j z‖)
  have hD : 0 ≤ D := mul_nonneg (by unfold expandingEmbeddingBound; positivity)
    (integral_nonneg (fun _ => norm_nonneg _))
  apply tendsto_weightedL2_of_pointwise_zero (D * M) V hV u
  · intro n y
    exact (expandingSmoothDerivative_physical_bound a k (L n) S ha ha1 hk (hL n) hS N j (f n) y).trans
      (mul_le_mul_of_nonneg_left (hf n) hD)
  · intro y
    let R := ‖y‖
    have hu := tendsto_expandingSmoothDerivative_local a k M 0 R S ha ha1 hk
      ((norm_nonneg (f 0)).trans (hf 0)) le_rfl hS N j L hL f hf (0 : C(E, ℂ))
      (by simp) (by simpa only [ContinuousMap.zero_apply, sub_zero] using hlocal)
    have hy : y ∈ Metric.closedBall (0 : E) R := by
      simp only [Metric.mem_closedBall, dist_zero_right, R, le_refl]
    have he := (ContinuousMap.evalCLM (R := ℂ) ⟨y, hy⟩).continuous.tendsto
      (schwartzBallConvolution R (smoothDerivativeKernel S hS N j) (0 : C(E, ℂ)))
    have hz : schwartzBallConvolution R (smoothDerivativeKernel S hS N j) (0 : C(E, ℂ)) = 0 := by
      ext x
      rw [schwartzBallConvolution_apply R 0 le_rfl _ _ (by simp)]
      simp
    have hh := he.comp hu
    change Tendsto (fun n => expandingPhysicalBall a k (L n) R ha ha1 hk (hL n)
      (expandingSmoothDerivative (L n) S hS N j (f n)) ⟨y, hy⟩) atTop _ at hh
    rw [hz] at hh
    simpa only [expandingPhysicalBall_apply, ContinuousMap.zero_apply, map_zero,
      expandingPhysicalContinuous_apply, u] using hh

end DefocusingNLS

end OAI
