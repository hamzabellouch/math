import OAI.Geometry.RCD.Coordinates.DyadicNormalizedGradient
import OAI.Geometry.RCD.Sobolev.ColumnGradientValueBound

namespace OAI

/-! # Lipschitz control in the same root-normalized harmonic coordinates -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem dyadic_root_lipschitz_bound {K : ℝ} (m : ℕ) (hm : 2 ≤ m+1)
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
    (z : Euclidean (m+1)) :
    ∀ x ∈ ball p ((2 : ℝ)^k*r/8), ∀ y ∈ ball p ((2 : ℝ)^k*r/8),
      |⟪v x-v y,A z⟫_ℝ| ≤
      (2*((m+1 : ℕ) : ℝ)*Real.sqrt ((2 : ℝ)^k)*‖z‖)*dist x y := by
  let L : ℝ≥0 := ⟨2*((m+1 : ℕ) : ℝ)*Real.sqrt ((2 : ℝ)^k)*‖z‖,by positivity⟩
  have hrad : 8*((2 : ℝ)^k*r/8) = 2^k*r := by ring
  have hgrad := dyadic_root_gradient_bound m hX ha hBG u p hr hε hε1 hsmall A hA k hscale hframes z
  have hL : (L : ℝ)^2 = 4*((m+1 : ℕ) : ℝ)^2*2^k*‖z‖^2 := by
    change (2*((m+1 : ℕ) : ℝ)*Real.sqrt ((2 : ℝ)^k)*‖z‖)^2 = _
    rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
    ring
  have hg : ∀ᵐ x ∂(hausdorff (m+1) X).restrict (ball p (8*((2 : ℝ)^k*r/8))),
      localGamma (hausdorff (m+1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic u (A z))
        (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic u (A z)) x ≤ (L : ℝ)^2 := by
    rw [hrad,hL]
    exact hgrad
  have hl := hX.continuous_local_gradient_lipschitz hm
    (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic u (A z))
    (fun x => ⟪v x,A z⟫_ℝ) p (by positivity : 0 < (2 : ℝ)^k*r/8) L
    (by rw [hrad]; exact hv.inner continuousOn_const)
    (by
      rw [hrad]
      exact sobolevColumnMap_representative (hausdorff (m+1) X)
        hX.quadratic u (ball p (2^k*r)) v hrep (A z)) hg
  intro x hx y hy
  have hh := hl.dist_le_mul x hx y hy
  have hLval : (L : ℝ) = 2*((m+1 : ℕ) : ℝ)*Real.sqrt ((2 : ℝ)^k)*‖z‖ := rfl
  rw [Real.dist_eq,hLval] at hh
  simpa only [inner_sub_left] using hh

end RegularPointCoordinates

end

end OAI
