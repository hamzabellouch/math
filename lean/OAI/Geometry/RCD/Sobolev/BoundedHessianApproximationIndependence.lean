import OAI.Geometry.RCD.Heat.BoundedHeatDiagonalHessianDifference
import OAI.Geometry.RCD.Sobolev.HessianL1LimitUniqueness
import OAI.Geometry.RCD.Sobolev.WeightedGradientPairDifference

namespace OAI

/-! # The local Hessian limit depends only on the limiting gradient -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem bounded_heat_hessian_approximation_independent (hK : K ≤ 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (u v : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (du dv : ℕ → Lp ℝ 2 (hausdorff n X))
    (hdu : ∀ k, IsWeakLaplacian (hausdorff n X) hX.quadratic (u k) (du k))
    (hdv : ∀ k, IsWeakLaplacian (hausdorff n X) hX.quadratic (v k) (dv k))
    (U V : ℕ → X → ℝ) (L M B C : ℕ → ℝ≥0)
    (hU : ∀ k, LipschitzWith (L k) (U k)) (hV : ∀ k, LipschitzWith (M k) (V k))
    (hu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) =ᵐ[hausdorff n X] U k)
    (hv : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (v k) =ᵐ[hausdorff n X] V k)
    (huB : ∀ k, ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x| ≤ B k)
    (hvC : ∀ k, ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic (v k) x| ≤ C k)
    {P : ℝ} (hP : 0 ≤ P)
    (hgu : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall p r),
      localGamma (hausdorff n X) hX.quadratic (u k) (u k) x ≤ P)
    (hgv : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall p r),
      localGamma (hausdorff n X) hX.quadratic (v k) (v k) x ≤ P)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ (hausdorff n X)) (D : ℝ≥0)
    (hD : ∀ᵐ x ∂hausdorff n X, |φ x| ≤ D)
    (hzero : ∀ x ∉ closedBall p r, φ x = 0)
    (z : SobolevSpace (hausdorff n X) hX.quadratic)
    (huE : Tendsto (fun k => weightedGamma (hausdorff n X) hX.quadratic
      (fun x => (φ x)^2) (u k-z) (u k-z)) atTop (𝓝 0))
    (hvE : Tendsto (fun k => weightedGamma (hausdorff n X) hX.quadratic
      (fun x => (φ x)^2) (v k-z) (v k-z)) atTop (𝓝 0))
    (WU WV UU VV : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hWU : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (WU k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)]
        localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) (u k))
    (hWV : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (WV k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)]
        localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) (v k))
    (hUU : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (UU k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)] localGamma (hausdorff n X) hX.quadratic (u k) (u k))
    (hVV : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (VV k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)] localGamma (hausdorff n X) hX.quadratic (v k) (v k))
    (I J : Lp ℝ 1 ((hausdorff n X).restrict (closedBall p r)))
    (hI : Tendsto (fun k => ∫ x in closedBall p r,
      |φ x*localHessianAction (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic a ha f) (u k) (u k) (WU k) (WU k) (UU k) x-I x|
      ∂hausdorff n X) atTop (𝓝 0))
    (hJ : Tendsto (fun k => ∫ x in closedBall p r,
      |φ x*localHessianAction (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic a ha f) (v k) (v k) (WV k) (WV k) (VV k) x-J x|
      ∂hausdorff n X) atTop (𝓝 0)) : I=J := by
  let m := hausdorff n X
  let q := hX.quadratic
  let w := heatSobolev m q a ha f
  have hD2 : ∀ᵐ x ∂m, ‖(φ x)^2‖ ≤ (D^2:ℝ≥0) := by
    filter_upwards [hD] with x hx
    simpa only [norm_pow,Real.norm_eq_abs,NNReal.coe_pow] using
      pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hE := weighted_gradient_pair_tendsto_zero m q (hφ.pow 2) hD2
    (Eventually.of_forall fun x => sq_nonneg (φ x)) u v z huE hvE
  have hd := hX.bounded_heat_diagonal_hessian_difference hn p hK f A hf ha hr
    u v du dv hdu hdv U V L M B C hU hV hu hv huB hvC hP hgu hgv
    φ hφ D hD hzero hE WU WV UU VV hWU hWV hUU hVV
  let F k x := φ x*localHessianAction m q w (u k) (u k) (WU k) (WU k) (UU k) x
  let G k x := φ x*localHessianAction m q w (v k) (v k) (WV k) (WV k) (VV k) x
  have hb : ∀ᵐ x ∂m, ‖φ x‖ ≤ D := by simpa only [Real.norm_eq_abs] using hD
  have hiF (k : ℕ) : Integrable (F k) (m.restrict (closedBall p r)) :=
    ((localHessianAction_integrable m q w (u k) (u k) (WU k) (WU k) (UU k)).bdd_mul hφ hb).integrableOn
  have hiG (k : ℕ) : Integrable (G k) (m.restrict (closedBall p r)) :=
    ((localHessianAction_integrable m q w (v k) (v k) (WV k) (WV k) (VV k)).bdd_mul hφ hb).integrableOn
  apply L1_limits_eq_of_difference (m.restrict (closedBall p r)) F G hiF hiG I J hI hJ
  apply hd.congr'
  refine Eventually.of_forall fun k => integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only [F,G]
  rw [mul_sub]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
