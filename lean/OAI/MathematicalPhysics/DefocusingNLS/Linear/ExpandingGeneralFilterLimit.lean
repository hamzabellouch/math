import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCompactPhysicalLimit

namespace OAI

/-! # Weighted compactness for an arbitrary fixed Schwartz Fourier filter -/

open Filter Topology MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance expandingGeneralFilterMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance expandingGeneralFilterProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (a k M : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
  (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
  (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
  (hlocal : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
    ‖expandingTorusFunction a k (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y))‖ < ε)

include hf hlocal

theorem tendsto_expandingSchwartzFilter_pointwise_zero (J : 𝓢(E, ℂ)) (y : E) :
    Tendsto (fun n => expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n)
      (expandingSchwartzFilter (L n) J (f n)) y) atTop (𝓝 0) := by
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hf 0)
  let C := expandingEmbeddingBound a k * M
  have hC : 0 ≤ C := mul_nonneg (by unfold expandingEmbeddingBound; positivity) hM
  let u := fun n => expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n) (f n)
  have hb (n : ℕ) (x : E) : ‖u n x‖ ≤ C :=
    (expandingPhysicalContinuous_norm_le a k (L n) ha ha1 hk (hL n) (f n) x).trans
      (mul_le_mul_of_nonneg_left (hf n) (by unfold expandingEmbeddingBound; positivity))
  have hc := tendsto_schwartzBallConvolution_zero ‖y‖ C hC J u hb
    (by simpa only [u, expandingPhysicalContinuous_apply] using hlocal)
  have hy : y ∈ Metric.closedBall (0 : E) ‖y‖ := by simp
  have he := (ContinuousMap.evalCLM (R := ℂ)
    (⟨y, hy⟩ : Metric.closedBall (0 : E) ‖y‖)).continuous.tendsto
      (0 : C(Metric.closedBall (0 : E) ‖y‖, ℂ))
  have hh := he.comp hc
  change Tendsto (fun n => schwartzBallConvolution ‖y‖ J (u n) ⟨y, hy⟩) atTop _ at hh
  have heq (n : ℕ) : schwartzBallConvolution ‖y‖ J (u n) ⟨y, hy⟩ =
      expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n)
        (expandingSchwartzFilter (L n) J (f n)) y :=
    (expandingSchwartzFilter_ball a k (L n) ‖y‖ ha ha1 hk (hL n) J (f n) ⟨y, hy⟩).symm
  simpa only [heq, map_zero] using hh

theorem tendsto_expandingSchwartzFilter_weightedL2 (J : 𝓢(E, ℂ))
    (V : E → ℂ) (hV : MemLp V 2 volume) :
    Tendsto (fun n => ∫ y : E, ‖V y *
      expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n)
        (expandingSchwartzFilter (L n) J (f n)) y‖ ^ 2) atTop (𝓝 0) := by
  let C := expandingEmbeddingBound a k * (∫ z : E, ‖J z‖)
  have hC : 0 ≤ C := mul_nonneg (by unfold expandingEmbeddingBound; positivity)
    (integral_nonneg (fun _ => norm_nonneg _))
  apply tendsto_weightedL2_of_pointwise_zero (C * M) V hV
    (fun n => expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n)
      (expandingSchwartzFilter (L n) J (f n))) ?_
    (tendsto_expandingSchwartzFilter_pointwise_zero a k M ha ha1 hk L hL f hf hlocal J)
  intro n y
  have hb := fourierBoundedMultiplier_norm_le (∫ z : E, ‖J z‖)
    (integral_nonneg (fun _ => norm_nonneg _))
    (fun m : frequencyLattice => radianFourierKernel J ((L n)⁻¹ • (m : E)))
    (fun _ => radianFourierKernel_norm_le_integral J _) (f n)
  calc
    _ ≤ expandingEmbeddingBound a k * ‖expandingSchwartzFilter (L n) J (f n)‖ :=
      expandingPhysicalContinuous_norm_le a k (L n) ha ha1 hk (hL n) _ y
    _ ≤ expandingEmbeddingBound a k * ((∫ z : E, ‖J z‖) * ‖f n‖) :=
      mul_le_mul_of_nonneg_left hb (by unfold expandingEmbeddingBound; positivity)
    _ = C * ‖f n‖ := (mul_assoc _ _ _).symm
    _ ≤ C * M := mul_le_mul_of_nonneg_left (hf n) hC

end DefocusingNLS

end OAI
