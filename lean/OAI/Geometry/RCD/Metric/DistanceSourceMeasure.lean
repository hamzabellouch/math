import OAI.Geometry.RCD.Sobolev.DistanceLaplacianInput
import OAI.Geometry.RCD.Metric.InwardLocality

namespace OAI

/-! # One actual distance source supplies both replacement and mass bounds -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The published distance Laplacian constructs the source. The checked
radial test then bounds that same source by the signed volume drop. -/
theorem distance_source_and_volume_drop {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (hdistance : LocalSquaredDistanceInput hX)
    {κ r : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K) (p : X) (hr : 0 < r)
    {model : ℝ → ℝ} (hBG : BallVolumeComparison (hausdorff n X) model)
    (hmodel : Continuous model) (hmodelr : 0 < model r) :
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∃ σ : Measure X, ∃ _hσ : IsFiniteMeasure σ,
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p (4 * r)),
        localGamma (hausdorff n X) hX.quadratic (inwardSobolev (hausdorff n X) hX.quadratic p (4 * r))
          (inwardSobolev (hausdorff n X) hX.quadratic p (4 * r)) x = 1) ∧
      ((r ^ (-(n : ℝ)) - (2 * r) ^ (-(n : ℝ))) / n) * σ.real (ball p r) ≤
        r ^ (-(n : ℝ)) * (hausdorff n X).real (ball p r) -
          (2 * r) ^ (-(n : ℝ)) * (hausdorff n X).real (ball p (2 * r)) +
          (κ * (4 * r) ^ 2) * ((r ^ (-(n : ℝ)) - (2 * r) ^ (-(n : ℝ))) / n) *
            (hausdorff n X).real (ball p (2 * r)) ∧
      ∀ (C : ℝ) (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (4 * r) C),
      ∀ (ψ : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ) (L : ℝ≥0),
        LipschitzWith L v → HasCompactSupport v → tsupport v ⊆ ball p r →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] v →
        energyForm (hausdorff n X) hX.quadratic
          (positiveSquaredDistance (hausdorff n X) hX.quadratic (by positivity : 0 ≤ 4 * r) χ) ψ +
          ((n : ℝ) + κ * (4 * r) ^ 2) * (∫ x in ball p r, v x ∂hausdorff n X) =
            ∫ x, v x ∂σ := by
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  obtain ⟨σ, hσ, heik, hsource⟩ := hdistance hn κ hκ hK p (4 * r) (by positivity)
  let _ := hσ
  have heik2 := inwardSobolev_eikonal_mono (hausdorff n X) hX.quadratic p
    (by linarith : 2 * r ≤ 4 * r) heik
  have hmass := squaredDistance_source_mass_le (hausdorff n X) hX.quadratic
    (by exact_mod_cast (by omega : 0 < n)) hr (by linarith : r < 2 * r)
    (by linarith : 2 * r < 4 * r) (by positivity : 0 ≤ κ * (4 * r) ^ 2)
    p σ hBG hmodel hmodelr ((ae_restrict_iff' measurableSet_ball).mp heik2) hsource
  refine ⟨σ, hσ, heik, hmass, ?_⟩
  intro C χ
  exact positiveSquaredDistance_source (hausdorff n X) hX.quadratic
    (by positivity : 0 ≤ 4 * r) χ (by linarith : r ≤ 4 * r) σ hsource

end RegularPointCoordinates

end

end OAI
