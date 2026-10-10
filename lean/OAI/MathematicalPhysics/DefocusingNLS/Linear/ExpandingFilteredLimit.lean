import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSmoothCutoff

namespace OAI

/-! # Smoothly filtered expanding-torus data converge on physical compact sets -/

open Filter Topology MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def expandingPhysicalBall (a k L R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    C(Metric.closedBall (0 : E) R, ℂ) :=
  shiftedBallRestriction R (expandingPhysicalContinuous a k L ha ha1 hk hL f) 0

@[simp] theorem expandingPhysicalBall_apply (a k L R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (f : FourierL2) (y : Metric.closedBall (0 : E) R) :
    expandingPhysicalBall a k L R ha ha1 hk hL f y =
      expandingTorusFunction a k L f (euclideanToTorus (L⁻¹ • (y : E))) := by
  change expandingPhysicalContinuous a k L ha ha1 hk hL f ((y : E) - 0) = _
  rw [sub_zero, expandingPhysicalContinuous_apply]

theorem expandingPhysicalBall_filter (a k L R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (K : 𝓢(E, ℂ)) (f : FourierL2) :
    expandingPhysicalBall a k L R ha ha1 hk hL (expandingSchwartzFilter L K f) =
      schwartzBallConvolution R K (expandingPhysicalContinuous a k L ha ha1 hk hL f) := by
  ext y
  change expandingPhysicalContinuous a k L ha ha1 hk hL (expandingSchwartzFilter L K f)
    ((y : E) - 0) = _
  rw [sub_zero]
  exact expandingSchwartzFilter_ball a k L R ha ha1 hk hL K f y

theorem tendsto_expandingPhysicalBall_filter (a k M M₀ R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (K : 𝓢(E, ℂ))
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M) (v : C(E, ℂ))
    (hv : ∀ y, ‖v y‖ ≤ M₀)
    (hlocal : ∀ S ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ S →
      ‖expandingTorusFunction a k (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y)) - v y‖ < ε) :
    Tendsto (fun n => expandingPhysicalBall a k (L n) R ha ha1 hk (hL n)
      (expandingSchwartzFilter (L n) K (f n))) atTop (𝓝 (schwartzBallConvolution R K v)) := by
  simp_rw [expandingPhysicalBall_filter]
  apply tendsto_schwartzBallConvolution R (expandingEmbeddingBound a k * M) M₀
    (by unfold expandingEmbeddingBound; positivity) hM₀ K
    (fun n => expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n) (f n)) v ?_ hv ?_
  · intro n y
    exact (expandingPhysicalContinuous_norm_le a k (L n) ha ha1 hk (hL n) (f n) y).trans
      (mul_le_mul_of_nonneg_left (hf n) (by unfold expandingEmbeddingBound; positivity))
  · simpa only [expandingPhysicalContinuous_apply] using hlocal

theorem tendsto_expandingPhysicalBall_smoothLow (a k M M₀ R S : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀) (hS : 0 < S)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M) (v : C(E, ℂ)) (hv : ∀ y, ‖v y‖ ≤ M₀)
    (hlocal : ∀ T ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ T →
      ‖expandingTorusFunction a k (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y)) - v y‖ < ε) :
    Tendsto (fun n => expandingPhysicalBall a k (L n) R ha ha1 hk (hL n)
      (expandingSmoothLow (L n) S hS (f n))) atTop
        (𝓝 (schwartzBallConvolution R (radianInverseKernel (smoothFrequencyCutoff S hS)) v)) := by
  simp_rw [expandingSmoothLow_eq_convolution]
  exact tendsto_expandingPhysicalBall_filter a k M M₀ R ha ha1 hk hM hM₀ L hL _ f hf v hv hlocal

end DefocusingNLS

end OAI
