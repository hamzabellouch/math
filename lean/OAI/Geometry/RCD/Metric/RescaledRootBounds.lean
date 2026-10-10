import OAI.Geometry.RCD.Coordinates.DyadicNormalizedLipschitz

namespace OAI

/-! # Boundedness and Lipschitz control after physical rescaling -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem dyadic_root_rescaled_bounds {K : ℝ} (m : ℕ) (hm : 2 ≤ m+1)
    (hX : NoncollapsedRCD K (m+1) X) {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m+1) X) (comparisonModelVolume m a))
    (u : Fin (m+1) → SobolevSpace (hausdorff (m+1) X) hX.quadratic)
    (v : X → Euclidean (m+1)) (p : X) {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hsmall : ((m+1 : ℕ) : ℝ)^2*(normalizationVolumeRatio m*ε) ≤ 1/2)
    (A : Euclidean (m+1) ≃L[ℝ] Euclidean (m+1))
    (hA : IsExactMeanNormalization (hausdorff (m+1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic u) (ball p r) measurableSet_ball A)
    (k : ℕ) (hscale : ∀ j ≤ k, a*(3*(2^j*r)) ≤ 1)
    (hframes : ∀ j ≤ k, ∃ (S : Euclidean (m+1) ≃L[ℝ] Euclidean (m+1))
      (w : X → Euclidean (m+1)),
      FirstOrderSplittingOn (hausdorff (m+1) X) hX.quadratic p (2^j*r) ε
        (transformedColumn (hausdorff (m+1) X) hX.quadratic u S) w ∧
      IsExactMeanNormalization (hausdorff (m+1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic u)
        (ball p (2^j*r)) measurableSet_ball S)
    (hv : ContinuousOn v (ball p (2^k*r)))
    (hrep : ∀ i, SobolevSpace.toLp (hausdorff (m+1) X) hX.quadratic (u i) =ᵐ[
      (hausdorff (m+1) X).restrict (ball p (2^k*r))] fun x => v x i)
    (z : Euclidean (m+1)) {S : ℝ} (_hS : 0 ≤ S) (hSk : S < (2 : ℝ)^k/8) :
    let C := 2*((m+1 : ℕ) : ℝ)*Real.sqrt ((2 : ℝ)^k)*‖z‖
    let f := fun x => ⟪v x-v p,A z⟫_ℝ/r
    (∀ x, dist x p ≤ S*r → |f x| ≤ C*S) ∧
    (∀ x y, dist x p ≤ S*r → dist y p ≤ S*r →
      |f x-f y| ≤ C*(dist x y/r)) := by
  let C := 2*((m+1 : ℕ) : ℝ)*Real.sqrt ((2 : ℝ)^k)*‖z‖
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hxball {x : X} (hx : dist x p ≤ S*r) : x ∈ ball p ((2 : ℝ)^k*r/8) := by
    have hh := mul_lt_mul_of_pos_right hSk hr
    rw [div_mul_eq_mul_div] at hh
    exact hx.trans_lt hh
  have hpb : p ∈ ball p ((2 : ℝ)^k*r/8) := mem_ball_self (by positivity)
  have hl := dyadic_root_lipschitz_bound m hm hX ha hBG u v p hr hε hε1 hsmall
    A hA k hscale hframes hv hrep z
  constructor
  · intro x hx
    change |⟪v x-v p,A z⟫_ℝ/r| ≤ C*S
    rw [abs_div,abs_of_pos hr]
    apply (div_le_iff₀ hr).mpr
    exact (hl x (hxball hx) p hpb).trans (by
      have hh := mul_le_mul_of_nonneg_left hx hC
      dsimp only [C] at *
      nlinarith only [hh])
  · intro x y hx hy
    change |⟪v x-v p,A z⟫_ℝ/r-⟪v y-v p,A z⟫_ℝ/r| ≤ C*(dist x y/r)
    have he : ⟪v x-v p,A z⟫_ℝ-⟪v y-v p,A z⟫_ℝ = ⟪v x-v y,A z⟫_ℝ := by
      simp only [inner_sub_left]
      ring
    rw [← sub_div,he,abs_div,abs_of_pos hr]
    exact (div_le_div_of_nonneg_right (hl x (hxball hx) y (hxball hy)) hr.le).trans_eq (by ring)

end RegularPointCoordinates

end

end OAI
