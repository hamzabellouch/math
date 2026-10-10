import OAI.Geometry.RCD.Coordinates.TransformationInput

namespace OAI

/-!
# Exact normalization retaining arbitrarily small splitting error

The two published harmonic inputs are applied with compatible thresholds.
Metric flatness supplies the no-extra-factor hypothesis by a proved finite
configuration argument. The resulting normalization acts on the actual
Sobolev column, and its pointwise coordinate map approximates the metric.
-/

open Set Metric MeasureTheory

noncomputable section

namespace RegularPointCoordinates

private theorem controlled_scaled_curvature_lower {K δ ε r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hδε : δ ≤ ε) (hε : 0 ≤ ε) (hcurv : -δ ≤ K * R ^ 2) : -ε ≤ K * r ^ 2 := by
  by_cases hK : 0 ≤ K
  · have hp := mul_nonneg hK (sq_nonneg r)
    linarith
  · have hs : r ^ 2 ≤ R ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonpos_left hs (le_of_not_ge hK)
    exact (neg_le_neg hδε).trans (hcurv.trans hm)

universe u

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A common threshold retains exact means, the prescribed first-order error,
and metric approximation at every interior scale. The extra quantitative
conclusion is already present in Huang--Huang Theorem 4.1(1). -/
theorem controlled_normalization_of_published_inputs {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (htrans : LocalTransformationInput hX) (hsplit : LocalFlatSplittingInput hX)
    {ρ β : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : X) (R : ℝ), 0 < R → -δ ≤ K * R ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2 * R) δ u v →
        (∀ s : ℝ, 0 < s → s ≤ R →
          ∃ f : X → Euclidean n, IsPointedApproximation p 0 s 2 δ f) →
        ∀ r : ℝ, 0 < r → 16 * r ≤ R → ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
          IsExactMeanNormalization (hausdorff n X) hX.quadratic
            (sobolevColumnMap (hausdorff n X) hX.quadratic u)
            (ball p (16 * r)) measurableSet_ball A ∧
          FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (16 * r) β
            (transformedColumn (hausdorff n X) hX.quadratic u A)
            (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
          IsPointedApproximation p 0 r (1 / 2) ρ
            (fun x => r⁻¹ • ((A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
              (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v p))) := by
  obtain ⟨τ, ε, hτ, hε, happ⟩ := hsplit hn ρ hρ
  let η : ℝ := 1 / (100 * ((n + 1 : ℕ) : ℝ) ^ 2)
  have hη : 0 < η := by dsimp [η]; positivity
  let ε' := min ε β
  have hε' : 0 < ε' := lt_min hε hβ
  obtain ⟨d, hd, hnormalize⟩ := htrans hn ε' η hε' hη
  let δ := min (d / 3) (min ε (min τ (η / 3)))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min hε (lt_min hτ (by positivity)))
  have hδd : 3 * δ ≤ d := by have h := min_le_left (d / 3) (min ε (min τ (η / 3))); dsimp [δ]; linarith
  have hδε : δ ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hδτ : δ ≤ τ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδη : 3 * δ ≤ η := by
    have h : δ ≤ η / 3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hδd' : δ ≤ d := by linarith
  refine ⟨δ, hδ, ?_⟩
  intro p R hR hcurv u v hu hflat r hr hrR
  have hgeometry (s : ℝ) (hs : 0 < s) (hsR : s ≤ R) :
      (∃ f : X → Euclidean n, IsPointedApproximation p 0 s 1 d f) ∧
        NoExtraEuclideanFactor n p s η := by
    obtain ⟨f, hf⟩ := hflat s hs hsR
    have hsmall := hf.restrict_radius hs (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 2) hδ.le
    exact ⟨⟨f, hsmall.mono_error hδd⟩,
      noExtraEuclideanFactor_of_approximation n hs (by positivity) hδη f hsmall⟩
  have hu' := hu.mono_error (hausdorff n X) hX.quadratic hδ.le hδd'
  obtain ⟨A, hAfirst, hAexact⟩ := hnormalize p R hR
    ((neg_le_neg hδd').trans hcurv) u v hu' hgeometry (16 * r) (by positivity) hrR
  have hAε := hAfirst.mono_error (hausdorff n X) hX.quadratic hε'.le (min_le_left _ _)
  have hAβ := hAfirst.mono_error (hausdorff n X) hX.quadratic hε'.le (min_le_right _ _)
  refine ⟨A, hAexact, hAβ, ?_⟩
  have hrR' : r ≤ R := by linarith
  have hcurv' : -ε ≤ K * r ^ 2 := controlled_scaled_curvature_lower hr hrR' hδε hε.le hcurv
  apply happ p r hr hcurv' (transformedColumn (hausdorff n X) hX.quadratic u A)
    (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) hAε
  obtain ⟨f, hf⟩ := hflat r hr hrR'
  exact ⟨f, hf.mono_error hδτ⟩

end RegularPointCoordinates

end

end OAI
