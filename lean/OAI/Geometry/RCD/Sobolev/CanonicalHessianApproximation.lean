import OAI.Geometry.RCD.Heat.CanonicalHeatHessian
import OAI.Geometry.RCD.Sobolev.BoundedHessianApproximationIndependence

namespace OAI

/-! # Every bounded regular gradient approximation has the canonical Hessian limit -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem hessian_limit_eq_canonical (hK : K ≤ 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (du : ℕ → Lp ℝ 2 (hausdorff n X))
    (hdu : ∀ k, IsWeakLaplacian (hausdorff n X) hX.quadratic (u k) (du k))
    (U : ℕ → X → ℝ) (L B : ℕ → ℝ≥0)
    (hU : ∀ k, LipschitzWith (L k) (U k))
    (hu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) =ᵐ[hausdorff n X] U k)
    (huB : ∀ k, ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x| ≤ B k)
    (v : SobolevSpace (hausdorff n X) hX.quadratic)
    (V : X → ℝ) (Lv Av : ℝ≥0) (hV : LipschitzWith Lv V) (hc : HasCompactSupport V)
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[hausdorff n X] V)
    (hAv : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic v x| ≤ Av)
    {P : ℝ} (hP : 0 ≤ P)
    (hgu : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall p r),
      localGamma (hausdorff n X) hX.quadratic (u k) (u k) x ≤ P)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ (hausdorff n X)) (D : ℝ≥0)
    (hD : ∀ᵐ x ∂hausdorff n X, |φ x| ≤ D)
    (hzero : ∀ x ∉ closedBall p r, φ x = 0)
    (henergy : Tendsto (fun k => weightedGamma (hausdorff n X) hX.quadratic
      (fun x => (φ x)^2) (u k-v) (u k-v)) atTop (𝓝 0))
    (WU UU : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hWU : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (WU k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)]
        localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) (u k))
    (hUU : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (UU k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)] localGamma (hausdorff n X) hX.quadratic (u k) (u k))
    (I J : Lp ℝ 1 ((hausdorff n X).restrict (closedBall p r)))
    (hI : Tendsto (fun k => ∫ x in closedBall p r,
      |φ x*localHessianAction (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic a ha f) (u k) (u k) (WU k) (WU k) (UU k) x-I x|
      ∂hausdorff n X) atTop (𝓝 0))
    (hcan : IsCanonicalHeatHessian (hausdorff n X) hX.quadratic
      (heatSobolev (hausdorff n X) hX.quadratic a ha f) v p r φ J) : I=J := by
  let m := hausdorff n X
  let q := hX.quadratic
  let w := heatSobolev m q a ha f
  obtain ⟨uc,dc,Uc,Mc,Pc,huc,hdc,hUc,hrepc,hBc,hPc,hgc,hconv⟩ :=
    hX.compact_lipschitz_heat_directions hn p v V Lv Av hV hc hv hAv
  obtain ⟨CW,CC,hCW,hCC,hJC⟩ := hcan
  have hCWr (k : ℕ) : SobolevSpace.toLp m q (CW k) =ᵐ[m.restrict (closedBall p r)]
      localGamma m q w (uc k) := by rw [huc k]; exact hCW k
  have hCCr (k : ℕ) : SobolevSpace.toLp m q (CC k) =ᵐ[m.restrict (closedBall p r)]
      localGamma m q (uc k) (uc k) := by rw [huc k]; exact hCC k
  have hJCr : Tendsto (fun k => ∫ x in closedBall p r,
      |φ x*localHessianAction m q w (uc k) (uc k) (CW k) (CW k) (CC k) x-J x| ∂m)
      atTop (𝓝 0) := by simpa only [huc] using hJC
  have hnconv : Tendsto (fun k => ‖uc k-v‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hconv.sub (tendsto_const_nhds (x := v))).norm
  have hD2 : ∀ᵐ x ∂m, ‖(φ x)^2‖ ≤ (D^2:ℝ≥0) := by
    filter_upwards [hD] with x hx
    simpa only [norm_pow,Real.norm_eq_abs,NNReal.coe_pow] using
      pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hEc : Tendsto (fun k => weightedGamma m q (fun x => (φ x)^2)
      (uc k-v) (uc k-v)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => weightedGamma_norm_le m q hD2 (uc k-v) (uc k-v))
    simpa only [mul_zero] using (hnconv.const_mul ((D^2:ℝ≥0):ℝ)).mul hnconv
  have hgu' (k : ℕ) : ∀ᵐ x ∂m.restrict (closedBall p r),
      localGamma m q (u k) (u k) x ≤ max P Pc :=
    (hgu k).mono fun x hx => hx.trans (le_max_left _ _)
  have hgc' (k : ℕ) : ∀ᵐ x ∂m.restrict (closedBall p r),
      localGamma m q (uc k) (uc k) x ≤ max P Pc :=
    (ae_restrict_of_ae (hgc k)).mono fun x hx => hx.trans (le_max_right _ _)
  exact hX.bounded_heat_hessian_approximation_independent hn p hK f A hf ha hr
    u uc du dc hdu hdc U Uc L Mc B (fun _ => Av) hU hUc hu hrepc huB hBc
    (hP.trans (le_max_left _ _)) hgu' hgc' φ hφ D hD hzero v henergy hEc
    WU CW UU CC hWU hCWr hUU hCCr I J hI hJCr

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
