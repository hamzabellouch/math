import OAI.Geometry.RCD.Heat.HeatDirectionApproximation
import OAI.Geometry.RCD.Heat.BoundedHeatHessianL1Limit

namespace OAI

/-! # A canonical Hessian action limit for compact Lipschitz directions -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem compact_lipschitz_hessian_limit (hK : K ≤ 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (v : SobolevSpace (hausdorff n X) hX.quadratic)
    (V : X → ℝ) (Lv Av : ℝ≥0) (hV : LipschitzWith Lv V) (hc : HasCompactSupport V)
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[hausdorff n X] V)
    (hAv : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic v x| ≤ Av)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ (hausdorff n X)) (D : ℝ≥0)
    (hD : ∀ᵐ x ∂hausdorff n X, |φ x| ≤ D)
    (hzero : ∀ x ∉ closedBall p r, φ x = 0) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ (u WU UU : ℕ → SobolevSpace m q) (J : Lp ℝ 1 (m.restrict (closedBall p r))),
      (∀ k, u k=heatH1 m q (1/(k+1:ℝ)) v) ∧
      (∀ k, SobolevSpace.toLp m q (WU k) =ᵐ[m.restrict (closedBall p r)] localGamma m q w (u k)) ∧
      (∀ k, SobolevSpace.toLp m q (UU k) =ᵐ[m.restrict (closedBall p r)] localGamma m q (u k) (u k)) ∧
      Tendsto (fun k => ∫ x in closedBall p r,
        |φ x*localHessianAction m q w (u k) (u k) (WU k) (WU k) (UU k) x-J x| ∂m)
        atTop (𝓝 0) := by
  intro m q w
  obtain ⟨u,d,U,M,P,hu,hd,hU,hrep,hB,hP,hgrad,hconv⟩ :=
    hX.compact_lipschitz_heat_directions hn p v V Lv Av hV hc hv hAv
  have hnconv : Tendsto (fun k => ‖u k-v‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hconv.sub (tendsto_const_nhds (x := v))).norm
  have hD2 : ∀ᵐ x ∂m, ‖(φ x)^2‖ ≤ (D^2:ℝ≥0) := by
    filter_upwards [hD] with x hx
    simpa only [norm_pow,Real.norm_eq_abs,NNReal.coe_pow] using
      pow_le_pow_left₀ (abs_nonneg _) hx 2
  have henergy : Tendsto (fun k => weightedGamma m q (fun x => (φ x)^2)
      (u k-v) (u k-v)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => weightedGamma_norm_le m q hD2 (u k-v) (u k-v))
    simpa only [mul_zero] using (hnconv.const_mul ((D^2:ℝ≥0):ℝ)).mul hnconv
  obtain ⟨σ,_hσ,hdata⟩ := hX.bounded_heat_mixed_hessian_density hn p hK f A hf ha hr
  choose WU WV UU hWU _hWV hUU _hbound using fun k =>
    hdata (u k) (d k) (hd k) (U k) (M k) Av (hU k) (hrep k) (hB k)
      (u k) (d k) (hd k) (U k) (M k) Av (hU k) (hrep k) (hB k)
  obtain ⟨J,hJ⟩ := hX.bounded_heat_hessian_L1_limit hn p hK f A hf ha hr u d hd U M
    (fun _ => Av) hU hrep hB hP (fun k => ae_restrict_of_ae (hgrad k))
    φ hφ D hD hzero v henergy WU UU hWU hUU
  exact ⟨u,WU,UU,J,hu,hWU,hUU,hJ⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
