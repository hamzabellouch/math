import OAI.Geometry.RCD.Metric.InnerBallValueMoments
import OAI.Geometry.RCD.Metric.MeasuredAnnularMass
import OAI.Geometry.RCD.Coordinates.Proper

namespace OAI

/-! # Quadratic value limits with the original outer mass normalization -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

private theorem cancel_middle_inverse (a b c : ℝ) (hb : b≠0) :
    a*b*(b⁻¹*c)=a*c := by
  calc _ = a*(b*b⁻¹)*c := by ring
       _ = _ := by rw [mul_inv_cancel₀ hb,mul_one]

theorem NoncollapsedRCD.outer_normalized_square_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S ρ τ : ℝ} (hS : 0<S) (hρ : 0<ρ)
    (hρτ : ρ<τ) (hτS : τ≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k)
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (hε : Tendsto ε atTop (𝓝 0))
    (u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (g : Euclidean n → ℝ) {L : ℝ≥0} (hg : LipschitzOnWith L g (closedBall 0 τ))
    (hu : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (ρ*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x-g (V k x)|≤η) :
    Tendsto (fun k => ((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (ρ*r k), (SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x)^2
        ∂hausdorff n X) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*∫ z in ball 0 ρ, (g z)^2)) := by
  have hρS := hρτ.le.trans hτS
  have hfin (k : ℕ) := (hX.finiteOnBounded (ball (p k) (S*r k)) isBounded_ball).ne
  have hpos (k : ℕ) : 0<(hausdorff n X).real (ball (p k) (S*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne' (hfin k)
  have hinner (k : ℕ) : 0<(hausdorff n X).real (ball (p k) (ρ*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hρ (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  have hi := inner_ball_value_moment_tendsto hS hρ hρτ hτS hr hV hfin hpos hinner hε
    (fun k => SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k))
    (fun k => SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k)) g g hg hg
    (fun k => by simpa only [← pow_two] using (Lp.memLp
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k))).integrable_sq.restrict) hu hu
  have hm := measured_ball_mass_tendsto hS hρ hρS hr hV hfin hpos hε
  have hVρ : volume.real (ball (0:Euclidean n) ρ)≠0 :=
    (ENNReal.toReal_pos (measure_ball_pos volume 0 hρ).ne' measure_ball_ne_top).ne'
  have ht := hm.mul hi
  simp only [← pow_two] at ht
  convert ht using 1
  · funext k
    have he := (hinner k).ne'
    exact (cancel_middle_inverse _ _ _ he).symm
  · congr 1
    exact (cancel_middle_inverse _ _ _ hVρ).symm

end RegularPointCoordinates

end

end OAI
