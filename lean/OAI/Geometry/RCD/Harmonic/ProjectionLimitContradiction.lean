import OAI.Geometry.RCD.Sobolev.PoissonHarmonicCompactnessInput
import OAI.Geometry.RCD.Sobolev.EulerOrthogonality

namespace OAI

/-! # Orthogonal residuals retain their nonzero norm in the limit -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
/-- Once the actual equation has been passed to the Euclidean limit,
the finite moments from the same compactness subsequence give the sharp
projection contradiction. Any nonzero normalization is allowed. -/
theorem PoissonHarmonicLimit.no_nonzero_orthogonal_euler_limit
    {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    {S : ℝ} {p : ℕ → X} {r : ℕ → ℝ}
    {u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic}
    {V : ℕ → X → Euclidean n} {w f : ℕ → SobolevSpace (hausdorff n X) hX.quadratic}
    {model : EuclideanHarmonicModel n S} (hlimit : PoissonHarmonicLimit hX S p r u V w f model)
    (hS : 0 < S) {ρ : ℝ} (hρ : 0 < ρ) (hρS : ρ < S)
    (L : Euclidean n →L[ℝ] ℝ) (k : ℝ)
    (heuler : ∀ x ∈ ball 0 S, fderiv ℝ model.value x x = model.value x + L x + k)
    {c : ℝ} (hc : c ≠ 0)
    (hnorm : Tendsto (fun i =>
      ⟪localAffineMomentFamily (hausdorff n X) hX.quadratic (u i) (w i)
          (ball (p i) (ρ * r i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) none,
        localAffineMomentFamily (hausdorff n X) hX.quadratic (u i) (w i)
          (ball (p i) (ρ * r i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) none⟫_ℝ)
      atTop (𝓝 c))
    (horth : ∀ i j,
      ⟪localAffineMomentFamily (hausdorff n X) hX.quadratic (u i) (w i)
          (ball (p i) (ρ * r i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) none,
        localAffineMomentFamily (hausdorff n X) hX.quadratic (u i) (w i)
          (ball (p i) (ρ * r i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (some j)⟫_ℝ = 0) :
    False := by
  have ho (j : Option (Fin n)) :
      ⟪model.moments hρS.le none, model.moments hρS.le (some j)⟫_ℝ = 0 := by
    have hz : Tendsto (fun i =>
        ⟪localAffineMomentFamily (hausdorff n X) hX.quadratic (u i) (w i)
            (ball (p i) (ρ * r i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) none,
          localAffineMomentFamily (hausdorff n X) hX.quadratic (u i) (w i)
            (ball (p i) (ρ * r i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (some j)⟫_ℝ)
        atTop (𝓝 0) := by
      simpa only [horth] using (tendsto_const_nhds : Tendsto (fun _i : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique (hlimit.moments ρ hρ hρS none (some j)) hz
  have hn := tendsto_nhds_unique hnorm (hlimit.moments ρ hρ hρS none none)
  exact hc (hn.trans (model.euler_orthogonal_norm_zero hS hρS.le L k heuler
    (ho none) (fun j => ho (some j))))

end RegularPointCoordinates

end

end OAI
