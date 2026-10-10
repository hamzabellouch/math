import OAI.Geometry.RCD.Coordinates.FiniteNormalizerGrowth
import OAI.Geometry.RCD.Coordinates.InitialAnalyticBounds

namespace OAI

/-! # Growth of the actual harmonic gradients in one root-normalized frame -/

open Set Metric MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem dyadic_root_gradient_bound {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m+1) X) {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m+1) X) (comparisonModelVolume m a))
    (u : Fin (m+1) → SobolevSpace (hausdorff (m+1) X) hX.quadratic)
    (p : X) {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
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
    (z : Euclidean (m+1)) :
    ∀ᵐ x ∂(hausdorff (m+1) X).restrict (ball p (2^k*r)),
      localGamma (hausdorff (m+1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic u (A z))
        (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic u (A z)) x
      ≤ 4*((m+1 : ℕ) : ℝ)^2*2^k*‖z‖^2 := by
  let μ := hausdorff (m+1) X
  let U := sobolevColumnMap μ hX.quadratic u
  obtain ⟨S,w,hfirst,hS⟩ := hframes k le_rfl
  have hrelative : ‖S.symm (A z)‖^2 ≤ (2 : ℝ)^k*‖z‖^2 := by
    rw [exact_mean_inverse_norm_sq μ hX.quadratic U (ball p (2^k*r)) measurableSet_ball S hS]
    have hh := (dyadic_mean_growth m hX ha hBG u p hr hε hsmall k hscale hframes (A z)).1
    simp only [pow_zero,one_mul] at hh
    rw [meanGram_energy_of_exact_normalization μ hX.quadratic U (ball p r) measurableSet_ball A hA,
      A.symm_apply_apply] at hh
    exact hh
  have hb := hfirst.directional_gradient μ hX.quadratic (S.symm (A z))
  rw [sobolevColumnMap_transformed] at hb
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,S.apply_symm_apply] at hb
  have hcoef : (((m+1 : ℕ) : ℝ)*(1+ε))^2 ≤ 4*((m+1 : ℕ) : ℝ)^2 :=
    splittingDirectionBound_sq_le hε hε1
  filter_upwards [hb] with x hx
  have hm := mul_le_mul hcoef hrelative (sq_nonneg _) (by positivity : 0 ≤ 4*((m+1 : ℕ) : ℝ)^2)
  exact hx.trans (by nlinarith only [hm])

end RegularPointCoordinates

end

end OAI
