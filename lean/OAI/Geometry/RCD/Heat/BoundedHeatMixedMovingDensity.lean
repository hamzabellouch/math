import OAI.Geometry.RCD.Heat.BoundedHeatMixedHessianDensity
import OAI.Geometry.RCD.Harmonic.WeightedMixedError

namespace OAI

/-! # Mixed Hessian errors under the actual bounded moving densities

Only the second direction has a uniform gradient bound. The first direction
has small energy against the same moving weight as the Hessian integral.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {Y : Type*} {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem bounded_heat_mixed_moving_density (hK : K ≤ 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (u v : ℕ → Y → SobolevSpace (hausdorff n X) hX.quadratic)
    (du dv : ℕ → Y → Lp ℝ 2 (hausdorff n X))
    (hdu : ∀ k t, IsWeakLaplacian (hausdorff n X) hX.quadratic (u k t) (du k t))
    (hdv : ∀ k t, IsWeakLaplacian (hausdorff n X) hX.quadratic (v k t) (dv k t))
    (U V : ℕ → Y → X → ℝ) (L M B C : ℕ → Y → ℝ≥0)
    (hU : ∀ k t, LipschitzWith (L k t) (U k t)) (hV : ∀ k t, LipschitzWith (M k t) (V k t))
    (hu : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k t) =ᵐ[hausdorff n X] U k t)
    (hv : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (v k t) =ᵐ[hausdorff n X] V k t)
    (huB : ∀ k t, ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k t) x| ≤ B k t)
    (hvC : ∀ k t, ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic (v k t) x| ≤ C k t)
    {P : ℝ} (hP : 0 ≤ P)
    (hgv : ∀ k t, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall p r),
      localGamma (hausdorff n X) hX.quadratic (v k t) (v k t) x ≤ P)
    (W : ℕ → Y → X → ℝ) (hW : ∀ k t, AEStronglyMeasurable (W k t) (hausdorff n X))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hWb : ∀ k t, ∀ᵐ x ∂hausdorff n X, 0 ≤ W k t x ∧ W k t x ≤ Cw)
    (hzero : ∀ k t x, x ∉ closedBall p r → W k t x = 0)
    (hE : TendstoUniformly (fun k t => weightedGamma (hausdorff n X) hX.quadratic (W k t) (u k t) (u k t))
      (fun _ => 0) atTop) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ WG WV GV : ℕ → Y → SobolevSpace m q,
      (∀ k t, SobolevSpace.toLp m q (WG k t) =ᵐ[m.restrict (closedBall p r)] localGamma m q w (u k t)) ∧
      (∀ k t, SobolevSpace.toLp m q (WV k t) =ᵐ[m.restrict (closedBall p r)] localGamma m q w (v k t)) ∧
      (∀ k t, SobolevSpace.toLp m q (GV k t) =ᵐ[m.restrict (closedBall p r)] localGamma m q (u k t) (v k t)) ∧
      TendstoUniformly (fun k t => ∫ x in closedBall p r, W k t x*
        |localHessianAction m q w (u k t) (v k t) (WG k t) (WV k t) (GV k t) x| ∂m)
        (fun _ => 0) atTop := by
  intro m q w
  classical
  let Ω := closedBall p r
  let ρ := m.restrict Ω
  obtain ⟨σ,hσ,hdata⟩ := hX.bounded_heat_mixed_hessian_density hn p hK f A hf ha hr
  let := hσ
  choose WG WV GV hWG hWV hGV hH using fun k t =>
    hdata (u k t) (du k t) (hdu k t) (U k t) (L k t) (B k t) (hU k t) (hu k t) (huB k t)
      (v k t) (dv k t) (hdv k t) (V k t) (M k t) (C k t) (hV k t) (hv k t) (hvC k t)
  let J x := (σ.rnDeriv m x).toReal
  let D x := P*J x
  let E k t := localGamma m q (u k t) (u k t)
  let H k t := localHessianAction m q w (u k t) (v k t) (WG k t) (WV k t) (GV k t)
  have hJi : Integrable J ρ := Measure.integrableOn_toReal_rnDeriv (μ := σ) (ν := m) (measure_ne_top σ Ω)
  have hDi : Integrable D ρ := hJi.const_mul P
  have hD0 : ∀ᵐ x ∂ρ, 0 ≤ D x := Eventually.of_forall fun x => mul_nonneg hP ENNReal.toReal_nonneg
  have hWnorm k t : ∀ᵐ x ∂m, ‖W k t x‖ ≤ Cw := (hWb k t).mono fun x hx => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hEi k t : Integrable (fun x => W k t x*E k t x) ρ :=
    ((localGamma_memL1 m q (u k t) (u k t)).bdd_mul (hW k t) (hWnorm k t)).integrableOn
  have hHi k t : Integrable (fun x => W k t x*|H k t x|) ρ :=
    ((localHessianAction_integrable m q w (u k t) (v k t) (WG k t) (WV k t) (GV k t)).abs.bdd_mul
      (hW k t) (hWnorm k t)).integrableOn
  have hpoint k t : ∀ᵐ x ∂ρ, 0 ≤ W k t x ∧ W k t x ≤ Cw ∧
      0 ≤ E k t x ∧ (H k t x)^2 ≤ D x*E k t x := by
    filter_upwards [ae_restrict_of_ae (hWb k t),hH k t,hgv k t,
      ae_restrict_of_ae (localGamma_self m q (u k t))] with x hw hh hv he
    have h0 : 0 ≤ E k t x := by dsimp only [E]; rw [he]; positivity
    refine ⟨hw.1,hw.2,h0,?_⟩
    have hb := mul_le_mul_of_nonneg_left hv
      (mul_nonneg (ENNReal.toReal_nonneg (a := σ.rnDeriv m x)) h0)
    dsimp only [H,D,E,J] at hh hb ⊢
    nlinarith only [hh,hb]
  have hElim : TendstoUniformly (fun k t => ∫ x, W k t x*E k t x ∂ρ) (fun _ => 0) atTop := by
    have he k t : (∫ x, W k t x*E k t x ∂ρ) = weightedGamma m q (W k t) (u k t) (u k t) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [hzero k t x hx,zero_mul]
    simpa only [he] using hE
  exact ⟨WG,WV,GV,hWG,hWV,hGV,weighted_mixed_error_vanishes ρ W E H D Cw hCw hDi hD0 hEi hHi hpoint hElim⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
