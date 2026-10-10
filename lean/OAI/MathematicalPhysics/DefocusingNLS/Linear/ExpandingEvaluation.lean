import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingNonlinearity

namespace OAI

/-! # Bounded observation for the exact expanding-torus model -/

open scoped ENNReal ComplexConjugate

namespace DefocusingNLS

noncomputable def expandingPointObservationVector (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (x : SchrodingerTorus) : FourierL2 :=
  ⟨fun n => (((expandingSobolevWeight a k L n)⁻¹ : ℝ) : ℂ) *
    conj (torusCharacter n x), by
    apply memℓp_gen
    have hs := (summable_expandingSobolevWeight_inv a k L ha ha1 hk hL).1.mul_left
      (((2 * Real.pi) ^ 12)⁻¹)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_conj,
      torusCharacter_norm_apply, mul_one, expanding_observation_weight_sq a k L hL] using hs⟩

noncomputable def expandingPointEvaluation (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (x : SchrodingerTorus) : FourierL2 →L[ℂ] ℂ :=
  innerSL ℂ (expandingPointObservationVector a k L ha ha1 hk hL x)

theorem hasSum_expandingPointEvaluation (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (x : SchrodingerTorus) (f : FourierL2) :
    HasSum (fun n => expandingFourierCoefficient a k L f n * torusCharacter n x)
      (expandingPointEvaluation a k L ha ha1 hk hL x f) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (expandingPointObservationVector a k L ha ha1 hk hL x) f
  simpa [expandingPointObservationVector, expandingPointEvaluation, expandingFourierCoefficient,
    RCLike.inner_apply', mul_assoc, mul_left_comm, mul_comm] using h

theorem expandingTorusFunction_eq_evaluation (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (x : SchrodingerTorus) (f : FourierL2) :
    expandingTorusFunction a k L f x = expandingPointEvaluation a k L ha ha1 hk hL x f := by
  rw [expandingTorusFunction_apply a k L ha ha1 hk hL]
  exact (hasSum_expandingPointEvaluation a k L ha ha1 hk hL x f).tsum_eq

/-- Evaluation has one operator-norm bound for every expanding torus and every point. -/
theorem expandingPointEvaluation_norm_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (x : SchrodingerTorus) :
    ‖expandingPointEvaluation a k L ha ha1 hk hL x‖ ≤ expandingEmbeddingBound a k := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  rw [← expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL]
  exact expandingTorusFunction_point_bound a k L ha ha1 hk hL f x

end DefocusingNLS

end OAI
