import OAI.Geometry.RCD.Sobolev.HessianSpanCommutator
import OAI.Geometry.RCD.Sobolev.PoissonPairSpan

namespace OAI

/-! # The Hessian commutator on the actual two-center Poisson span -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The same-scale replacements and harmonic coordinates give the actual
common-span commutator estimate, with their full Bochner measures. -/
theorem actual_poisson_commutator_span {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianActionInput hX)
    {κ B J C A epsilon r0 : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (hA : 0 ≤ A) (hepsilon : 0 ≤ epsilon) (p₁ p₂ z : X)
    (S₁ : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p₁ r0)
    (S₂ : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p₂ r0)
    (T₁ : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S₁ B J C)
    (T₂ : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S₂ B J C)
    (i : ℕ)
    (hroom₁ : dist z p₁ ≤ distanceSourceRadius r0 i / 4)
    (hroom₂ : dist z p₂ ≤ distanceSourceRadius r0 i / 4)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball z (distanceSourceRadius r0 i / 4)) (u j))
    (hgrad : ∀ j, ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ (1 + epsilon) ^ 2)
    (hf₁ : ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T₁.replacement i) (T₁.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (hf₂ : ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T₂.replacement i) (T₂.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2) :
    let s := distanceSourceRadius r0 i
    let f : Fin 2 → SobolevSpace (hausdorff n X) hX.quadratic :=
      ![T₁.replacement i, T₂.replacement i]
    let U := sobolevColumnMap (hausdorff n X) hX.quadratic
      (poissonSpan (hausdorff n X) hX.quadratic u f)
    let ell := poissonSpanLaplacian n ((n : ℝ) + κ * (4 * s) ^ 2)
    ∃ L : ℝ≥0, (L : ℝ) = ((n + 2 : ℕ) : ℝ) * max (1 + epsilon) (A * s) ∧
      ∃ M : PositiveBilinearMeasure X (Euclidean (n + 2)),
        (∀ v, Nonempty (LocalHarmonicEnergy (hausdorff n X) hX.quadratic U M κ z (s / 32) L v)) ∧
        ShiftedBochnerLowerBound M ((hausdorff n X).restrict (ball z (2 * (s / 32)))) ell n ∧
        ∀ t : ℝ, 0 < t → t ≤ 2 * (s / 32) →
          ∃ G : ∀ v w, LocalHessianPairing (hausdorff n X) hX.quadratic
            (ball z t) (U v) (U w),
          ∀ v w a (Cv Cw Ca : ℝ), 0 ≤ Cv → 0 ≤ Cw → 0 ≤ Ca →
            (∀ᵐ x ∂(hausdorff n X).restrict (ball z t),
              localGamma (hausdorff n X) hX.quadratic (U v) (U v) x ≤ Cv ^ 2) →
            (∀ᵐ x ∂(hausdorff n X).restrict (ball z t),
              localGamma (hausdorff n X) hX.quadratic (U w) (U w) x ≤ Cw ^ 2) →
            (∀ᵐ x ∂(hausdorff n X).restrict (ball z t),
              localGamma (hausdorff n X) hX.quadratic (U a) (U a) x ≤ Ca ^ 2) →
            (∫ x in ball z t,
              (localGamma (hausdorff n X) hX.quadratic (U w) (G v a).mixed x -
                localGamma (hausdorff n X) hX.quadratic (U v) (G w a).mixed x -
                localGamma (hausdorff n X) hX.quadratic (U w) (U a) x) ^ 2 ∂hausdorff n X) ≤
              2 * ((Cw ^ 2 * Ca ^ 2) *
                ((M.measure v).real (ball z t) -
                  (2 * ell v - (n : ℝ)) * (hausdorff n X).real (ball z t))) +
              2 * ((Cv ^ 2 * Ca ^ 2) * (M.measure w).real (ball z t)) := by
  let s := distanceSourceRadius r0 i
  have hs : 0 < s := distanceSourceRadius_pos S₁.radius_pos i
  let f : Fin 2 → SobolevSpace (hausdorff n X) hX.quadratic :=
    ![T₁.replacement i, T₂.replacement i]
  let G₀ := max (1 + epsilon) (A * s)
  have hG₀ : 0 ≤ G₀ := (by linarith : 0 ≤ 1 + epsilon).trans (le_max_left _ _)
  let L : ℝ≥0 := ⟨((n + 2 : ℕ) : ℝ) * G₀, mul_nonneg (Nat.cast_nonneg _) hG₀⟩
  refine ⟨L, rfl, ?_⟩
  apply hhessian.span_commutator_directional hκ hK z (s / 32) (by positivity) L
    (sobolevColumnMap (hausdorff n X) hX.quadratic
      (poissonSpan (hausdorff n X) hX.quadratic u f))
    (poissonSpanLaplacian n ((n : ℝ) + κ * (4 * s) ^ 2))
  · intro v
    rw [show 8 * (s / 32) = s / 4 by ring]
    apply poissonSpan_constant_laplacian (hausdorff n X) hX.quadratic u f _ hu
    intro j
    fin_cases j
    · exact T₁.laplacian_on_ball (hausdorff n X) hX.quadratic i z (by change s / 4 + dist z p₁ ≤ s; change dist z p₁ ≤ s / 4 at hroom₁; linarith)
    · exact T₂.laplacian_on_ball (hausdorff n X) hX.quadratic i z (by change s / 4 + dist z p₂ ≤ s; change dist z p₂ ≤ s / 4 at hroom₂; linarith)
  · intro v
    rw [show 8 * (s / 32) = s / 4 by ring]
    apply poissonSpan_gradient (hausdorff n X) hX.quadratic u f G₀
    · intro j
      filter_upwards [hgrad j] with x hx
      exact hx.trans ((sq_le_sq₀ (by linarith) hG₀).mpr (le_max_left _ _))
    · intro j
      have hj : ∀ᵐ x ∂(hausdorff n X).restrict (ball z (s / 4)),
          localGamma (hausdorff n X) hX.quadratic (f j) (f j) x ≤ (A * s) ^ 2 := by
        fin_cases j
        · exact hf₁
        · exact hf₂
      filter_upwards [hj] with x hx
      exact hx.trans ((sq_le_sq₀ (mul_nonneg hA hs.le) hG₀).mpr (le_max_right _ _))

end RegularPointCoordinates

end

end OAI
