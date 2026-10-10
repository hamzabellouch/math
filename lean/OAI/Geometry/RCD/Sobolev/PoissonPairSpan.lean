import OAI.Geometry.RCD.Sobolev.PoissonFamilyGradient
import OAI.Geometry.RCD.Sobolev.PoissonSpan

namespace OAI

/-! # The shared Hessian span of two actual same-scale replacements -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The harmonic column and the two actual replacements admit one shared
full Bochner measure and the shifted Hessian pairing bounds. -/
theorem actual_poisson_pair_span {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianInput hX)
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
        ∀ v w (t : ℝ), 0 < t → t ≤ 2 * (s / 32) →
          ∃ G : LocalHessianPairing (hausdorff n X) hX.quadratic
            (ball z t) (U v) (U w),
          ∀ b : ℝ, ∀ φ : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball z t),
            (G.hessian φ - b * energyForm (hausdorff n X) hX.quadratic (U w) φ.val) ^ 2 ≤
              ((L : ℝ) ^ 2 * ‖w‖ ^ 2 *
                ((M.measure v).real (ball z t) -
                  (2 * b * ell v - (n : ℝ) * b ^ 2) *
                    (hausdorff n X).real (ball z t))) *
                energyForm (hausdorff n X) hX.quadratic φ.val φ.val := by
  let s := distanceSourceRadius r0 i
  have hs : 0 < s := distanceSourceRadius_pos S₁.radius_pos i
  let f : Fin 2 → SobolevSpace (hausdorff n X) hX.quadratic :=
    ![T₁.replacement i, T₂.replacement i]
  let G₀ := max (1 + epsilon) (A * s)
  have hG₀ : 0 ≤ G₀ := (by linarith : 0 ≤ 1 + epsilon).trans (le_max_left _ _)
  let L : ℝ≥0 := ⟨((n + 2 : ℕ) : ℝ) * G₀, mul_nonneg (Nat.cast_nonneg _) hG₀⟩
  refine ⟨L, rfl, ?_⟩
  apply hhessian κ hκ hK z (s / 32) (by positivity) L
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
