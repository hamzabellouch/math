import OAI.Geometry.RCD.Coordinates.ControlledNormalization
import OAI.Geometry.RCD.Harmonic.FirstOrderLocalization
import OAI.Geometry.RCD.Metric.UniformVolumeRatio

namespace OAI

/-!
# Uniform normalization at nearby centers

A single harmonic map on the enlarged initial ball supplies the maps at all
nearby centers. Only the volume-ratio cost is paid when its first-order
splitting data are restricted. The resulting normalizers and approximation
bounds are uniform in the center and in every smaller scale.
-/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Uniform first-order data and all-center flatness give actual normalized
harmonic coordinates at every center in the inner quarter-ball. -/
theorem uniform_controlled_coordinates {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (htrans : LocalTransformationInput hX) (hsplit : LocalFlatSplittingInput hX)
    {ρ β C : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) (hC : 1 ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : X) (R : ℝ), 0 < R → -δ ≤ K * R ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2 * R) δ u v →
        (∀ q ∈ ball p (R / 4),
          (hausdorff n X).real (ball p (2 * R)) ≤
            C * (hausdorff n X).real (ball q (R / 2))) →
        (∀ q ∈ ball p (R / 4), ∀ s : ℝ, 0 < s → s ≤ R / 4 →
          ∃ f : X → Euclidean n, IsPointedApproximation q 0 s 2 δ f) →
        ∀ q ∈ ball p (R / 4), ∀ r : ℝ, 0 < r → 64 * r ≤ R →
          ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
            IsExactMeanNormalization (hausdorff n X) hX.quadratic
              (sobolevColumnMap (hausdorff n X) hX.quadratic u)
              (ball q (16 * r)) measurableSet_ball A ∧
            FirstOrderSplittingOn (hausdorff n X) hX.quadratic q (16 * r) β
              (transformedColumn (hausdorff n X) hX.quadratic u A)
              (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
            IsPointedApproximation q 0 r (1 / 2) ρ
              (fun x => r⁻¹ • ((A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
                (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v q))) := by
  obtain ⟨d, hd, hnormalize⟩ := controlled_normalization_of_published_inputs hX hn htrans hsplit hρ hβ
  have hCpos : 0 < C := by linarith
  let δ := d / C
  have hδ : 0 < δ := div_pos hd hCpos
  have hδd : δ ≤ d := by
    apply (div_le_iff₀ hCpos).mpr
    nlinarith
  have hCd : C * δ = d := by dsimp [δ]; field_simp
  refine ⟨δ, hδ, ?_⟩
  intro p R hR hcurv u v hu hvol hflat q hq r hr hrR
  have hsub : ball q (R / 2) ⊆ ball p (2 * R) := by
    intro x hx
    have hx' := mem_ball.mp hx
    have hq' := mem_ball.mp hq
    have ht := dist_triangle x q p
    apply mem_ball.mpr
    linarith
  have hlocal := hu.restrict_ball (hausdorff n X) hX.quadratic hsub hδ.le hC
    (ne_of_gt (hX.fullSupport q (R / 2) (by positivity)))
    (ne_of_lt (hX.finiteOnBounded (ball q (R / 2)) isBounded_ball))
    (ne_of_gt (hX.fullSupport p (2 * R) (by positivity)))
    (ne_of_lt (hX.finiteOnBounded (ball p (2 * R)) isBounded_ball)) (hvol q hq)
  rw [hCd] at hlocal
  have hcurv' : -d ≤ K * (R / 4) ^ 2 := by
    by_cases hK : 0 ≤ K
    · have hp := mul_nonneg hK (sq_nonneg (R / 4))
      linarith
    · have hs : (R / 4) ^ 2 ≤ R ^ 2 := by nlinarith
      have hm := mul_le_mul_of_nonpos_left hs (le_of_not_ge hK)
      linarith
  have hlocal' : FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      q (2 * (R / 4)) d u v := by
    convert hlocal using 1
    ring
  apply hnormalize q (R / 4) (by positivity) hcurv' u v hlocal'
  · intro s hs hsR
    obtain ⟨f, hf⟩ := hflat q hq s hs hsR
    exact ⟨f, hf.mono_error hδd⟩
  · exact hr
  · linarith

/-- The volume-ratio premise is supplied by Bishop--Gromov with a fixed
constant depending only on dimension. -/
theorem uniform_controlled_coordinates_of_comparison {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 1) X) (hn : 2 ≤ m + 1)
    (htrans : LocalTransformationInput hX) (hsplit : LocalFlatSplittingInput hX)
    {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    {ρ β : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : X) (R : ℝ), 0 < R → -δ ≤ K * R ^ 2 →
      a * (3 * R) ≤ 1 →
      ∀ (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
        (v : X → Euclidean (m + 1)),
        FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p (2 * R) δ u v →
        (∀ q ∈ ball p (R / 4), ∀ s : ℝ, 0 < s → s ≤ R / 4 →
          ∃ f : X → Euclidean (m + 1), IsPointedApproximation q 0 s 2 δ f) →
        ∀ q ∈ ball p (R / 4), ∀ r : ℝ, 0 < r → 64 * r ≤ R →
          ∃ A : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1),
            IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
              (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
              (ball q (16 * r)) measurableSet_ball A ∧
            FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic q (16 * r) β
              (transformedColumn (hausdorff (m + 1) X) hX.quadratic u A)
              (fun x => (A : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v x)) ∧
            IsPointedApproximation q 0 r (1 / 2) ρ
              (fun x => r⁻¹ • ((A : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v x) -
                (A : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint (v q))) := by
  obtain ⟨δ, hδ, happly⟩ := uniform_controlled_coordinates hX hn htrans hsplit hρ hβ
    (normalizationVolumeRatio_ge_one m)
  refine ⟨δ, hδ, ?_⟩
  intro p R hR hcurv hscale u v hu hflat
  exact happly p R hR hcurv u v hu
    (fun q hq => nearby_normalization_volume_ratio m hX ha hBG hR hscale hq) hflat

end RegularPointCoordinates

end

end OAI
