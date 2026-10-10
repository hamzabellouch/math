import OAI.Geometry.RCD.Heat.BoundedHeatMixedHessianDensity
import OAI.Geometry.RCD.Sobolev.BoundedEnergyIntegrableWeight
import OAI.Geometry.RCD.Harmonic.QuadraticErrorL1Limit

namespace OAI

/-! # Vanishing mixed Hessian errors in bounded regular directions

The first direction has vanishing local energy. A fixed Bochner density
and uniform gradient bounds give absolute L1 convergence of its mixed
Hessian pairing with every uniformly bounded second direction.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem bounded_heat_mixed_hessian_vanishes (hK : K ≤ 0)
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
    {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hgu : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall p r),
      localGamma (hausdorff n X) hX.quadratic (u k) (u k) x ≤ P)
    (hgv : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall p r),
      localGamma (hausdorff n X) hX.quadratic (v k) (v k) x ≤ Q)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ (hausdorff n X)) (D : ℝ≥0)
    (hD : ∀ᵐ x ∂hausdorff n X, |φ x| ≤ D)
    (hzero : ∀ x ∉ closedBall p r, φ x = 0)
    (henergy : Tendsto (fun k => weightedGamma (hausdorff n X) hX.quadratic
      (fun x => (φ x)^2) (u k) (u k)) atTop (𝓝 0)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ WG WV GV : ℕ → SobolevSpace m q,
      (∀ k, SobolevSpace.toLp m q (WG k) =ᵐ[m.restrict (closedBall p r)] localGamma m q w (u k)) ∧
      (∀ k, SobolevSpace.toLp m q (WV k) =ᵐ[m.restrict (closedBall p r)] localGamma m q w (v k)) ∧
      (∀ k, SobolevSpace.toLp m q (GV k) =ᵐ[m.restrict (closedBall p r)] localGamma m q (u k) (v k)) ∧
      Tendsto (fun k => ∫ x in closedBall p r,
        |φ x*localHessianAction m q w (u k) (v k) (WG k) (WV k) (GV k) x| ∂m) atTop (𝓝 0) := by
  intro m q w
  let Ω := closedBall p r
  let ρ := m.restrict Ω
  let : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr (isCompact_closedBall p r).measure_lt_top.ne
  obtain ⟨σ,hσ,hdata⟩ := hX.bounded_heat_mixed_hessian_density hn p hK f A hf ha hr
  let := hσ
  choose WG WV GV hWG hWV hGV hH using fun k =>
    hdata (u k) (du k) (hdu k) (U k) (L k) (B k) (hU k) (hu k) (huB k)
      (v k) (dv k) (hdv k) (V k) (M k) (C k) (hV k) (hv k) (hvC k)
  let E k x := (φ x)^2*localGamma m q (u k) (u k) x
  let J x := (σ.rnDeriv m x).toReal
  have hJ : Integrable J ρ := Measure.integrableOn_toReal_rnDeriv (μ := σ) (ν := m) (measure_ne_top σ Ω)
  have hφ2 : ∀ᵐ x ∂m, ‖(φ x)^2‖ ≤ (D:ℝ)^2 := by
    filter_upwards [hD] with x hx
    simpa only [norm_pow,Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hEi (k : ℕ) : Integrable (E k) ρ :=
    ((localGamma_memL1 m q (u k) (u k)).bdd_mul (hφ.pow 2) hφ2).integrableOn
  have hEb (k : ℕ) : ∀ᵐ x ∂ρ, 0 ≤ E k x ∧ E k x ≤ (D:ℝ)^2*P := by
    filter_upwards [hgu k,ae_restrict_of_ae hD,
      ae_restrict_of_ae (localGamma_self m q (u k))] with x hg hd he
    have h0 : 0 ≤ localGamma m q (u k) (u k) x := by rw [he]; positivity
    refine ⟨mul_nonneg (sq_nonneg _) h0,?_⟩
    have hd2 : (φ x)^2 ≤ (D:ℝ)^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hd 2
    exact mul_le_mul hd2 hg h0 (sq_nonneg _)
  have hElim : Tendsto (fun k => ∫ x, E k x ∂ρ) atTop (𝓝 0) := by
    have he (k : ℕ) : (∫ x, E k x ∂ρ) = weightedGamma m q (fun x => (φ x)^2) (u k) (u k) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      dsimp only [E]
      rw [hzero x hx]
      simp only [zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul]
    simpa only [he] using henergy
  have hJEi (k : ℕ) : Integrable (fun x => J x*E k x) ρ := by
    have hh := hJ.bdd_mul (hEi k).aestronglyMeasurable (hEb k |>.mono fun x hx => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2)
    exact hh.congr (Eventually.of_forall fun _ => mul_comm _ _)
  have hJElim := bounded_energy_integrable_weight ρ E hEi (mul_nonneg (sq_nonneg _) hP) hEb hElim J hJ
  let H k x := φ x*localHessianAction m q w (u k) (v k) (WG k) (WV k) (GV k) x
  have hHi (k : ℕ) : Integrable (H k) ρ :=
    ((localHessianAction_integrable m q w (u k) (v k) (WG k) (WV k) (GV k)).bdd_mul hφ
      (hD.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)).integrableOn
  have hb (k : ℕ) : ∀ᵐ x ∂ρ, (H k x)^2 ≤ Q*(J x*E k x) := by
    filter_upwards [hH k,hgv k,ae_restrict_of_ae (localGamma_self m q (u k))] with x hx hv he
    have h0 : 0 ≤ localGamma m q (u k) (u k) x := by rw [he]; positivity
    have hj : 0 ≤ J x := ENNReal.toReal_nonneg
    have hh := mul_le_mul_of_nonneg_left hx (sq_nonneg (φ x))
    have hv' := mul_le_mul_of_nonneg_left hv (mul_nonneg (sq_nonneg (φ x)) (mul_nonneg hj h0))
    dsimp only [H,E,J] at hh hv' ⊢
    rw [mul_pow]
    nlinarith only [hh,hv']
  exact ⟨WG,WV,GV,hWG,hWV,hGV,quadratic_error_L1_limit ρ H (fun k x => J x*E k x)
    hHi hJEi hQ hb hJElim⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
