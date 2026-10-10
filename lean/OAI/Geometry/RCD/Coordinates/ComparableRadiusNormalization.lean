import OAI.Geometry.RCD.Coordinates.InitialAnalyticBounds
import OAI.Geometry.RCD.Coordinates.NormalizedMeanDirectionError
import OAI.Geometry.RCD.Metric.RescaledBallVolume
import OAI.Geometry.RCD.Harmonic.FirstOrderLocalization

namespace OAI

/-! # Constructed exact normalizers at every comparable inner radius -/

open Set Metric MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.interior_radius_normalization {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ C : ℝ, 1≤C ∧ ∀ (p : X) (R ε : ℝ), 0 < R → -1≤K*(2*R)^2 →
      0≤ε → (n:ℝ)^2*(C*ε)≤1/2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2*R) ε u v →
      ∀ t : ℝ, τ*R≤t → t≤R →
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p t (C*ε) u v ∧
        ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
        IsExactMeanNormalization (hausdorff n X) hX.quadratic
          (sobolevColumnMap (hausdorff n X) hX.quadratic u) (ball p t) measurableSet_ball A ∧
        ‖(A : Euclidean n →L[ℝ] Euclidean n)‖^2≤2 ∧
        ∀ z : Euclidean n,
          ((hausdorff n X).real (ball p t))⁻¹*(∫ x in ball p t,
            |localGamma (hausdorff n X) hX.quadratic
              (sobolevColumnMap (hausdorff n X) hX.quadratic u (A z))
              (sobolevColumnMap (hausdorff n X) hX.quadratic u (A z)) x-‖z‖^2| ∂hausdorff n X)
          ≤4*(n:ℝ)^2*(C*ε)*‖z‖^2 := by
  obtain ⟨C,hC,hvolume⟩ := hX.rescaled_ball_volume_factor hn
    (a:=1) (δ:=τ/2) zero_le_one (by positivity) (by linarith)
  refine ⟨C,hC,?_⟩
  intro p R ε hR hcurv hε hsmall u v hfirst t ht htR
  let μ := hausdorff n X
  have ht0 : 0<t := lt_of_lt_of_le (by positivity : 0<τ*R) ht
  have hm : μ.real (ball p (2*R))≤C*μ.real (ball p t) := by
    have hv := hvolume p (2*R) (by positivity) hcurv p (by simp; positivity)
    have hs : (τ/2)*(2*R)≤t := by linarith
    exact hv.trans (mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (hX.finiteOnBounded _ isBounded_ball).ne
        (measure_mono (ball_subset_ball hs))) (zero_le_one.trans hC))
  have hz : μ (ball p t)≠0 := (hX.fullSupport p t ht0).ne'
  have hf : μ (ball p t)≠⊤ := (hX.finiteOnBounded _ isBounded_ball).ne
  have hlarge0 : μ (ball p (2*R))≠0 := (hX.fullSupport _ _ (by positivity)).ne'
  have hlargef : μ (ball p (2*R))≠⊤ := (hX.finiteOnBounded _ isBounded_ball).ne
  have hsub : ball p t⊆ball p (2*R) := ball_subset_ball (by linarith)
  have hrestricted := hfirst.restrict_ball μ hX.quadratic hsub hε hC hz hf hlarge0 hlargef hm
  obtain ⟨A,hA⟩ := exists_exact_mean_normalization_of_gram_error μ hX.quadratic u (ball p t)
    measurableSet_ball hz hf (mul_nonneg (zero_le_one.trans hC) hε)
    (lt_of_le_of_lt hsmall (by norm_num)) hrestricted.gram
  refine ⟨hrestricted,A,hA,?_,?_⟩
  · exact initial_normalizer_norm_sq_le_two μ hX.quadratic u hfirst (ball p t)
      measurableSet_ball hsub hz hf hlarge0 hlargef hC hε hm hsmall A hA
  · exact normalized_mean_direction_error μ hX.quadratic u (ball p t) measurableSet_ball
      hz hf (mul_nonneg (zero_le_one.trans hC) hε) hsmall hrestricted.gram A hA

theorem NoncollapsedRCD.comparable_radius_normalization {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) :
    ∃ C : ℝ, 1≤C ∧ ∀ (p : X) (R ε : ℝ), 0 < R → -1≤K*(2*R)^2 →
      0≤ε → (n:ℝ)^2*(C*ε)≤1/2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2*R) ε u v →
      ∀ t : ℝ, R/2≤t → t≤R →
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p t (C*ε) u v ∧
        ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
        IsExactMeanNormalization (hausdorff n X) hX.quadratic
          (sobolevColumnMap (hausdorff n X) hX.quadratic u) (ball p t) measurableSet_ball A ∧
        ‖(A : Euclidean n →L[ℝ] Euclidean n)‖^2≤2 ∧
        ∀ z : Euclidean n,
          ((hausdorff n X).real (ball p t))⁻¹*(∫ x in ball p t,
            |localGamma (hausdorff n X) hX.quadratic
              (sobolevColumnMap (hausdorff n X) hX.quadratic u (A z))
              (sobolevColumnMap (hausdorff n X) hX.quadratic u (A z)) x-‖z‖^2| ∂hausdorff n X)
          ≤4*(n:ℝ)^2*(C*ε)*‖z‖^2 := by
  simpa only [show ∀ R : ℝ, (1/2)*R=R/2 by intro R; ring] using
    hX.interior_radius_normalization hn (1/2) (by norm_num) (by norm_num)

end RegularPointCoordinates

end

end OAI
