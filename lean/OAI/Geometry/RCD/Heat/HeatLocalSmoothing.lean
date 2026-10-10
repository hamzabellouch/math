import OAI.Geometry.RCD.Heat.HeatParabolicSmall

namespace OAI

/-! # Local L²-to-L∞ smoothing without a heat-kernel hypothesis

The parabolic small-mass bound is normalized using L² contraction.
Both signs are tested, so the result applies to arbitrary real L² data.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heat_set_time_L2_bound (f : Lp ℝ 2 μ) {S : Set X} (hS : MeasurableSet S)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ∫ x in S, (heatAt μ hQ t f x)^2 ∂μ) ≤ (b-a)*‖f‖^2 := by
  have hc := continuous_setIntegral_sq_path μ (heatAt_continuous μ hQ f) hS
  have ht (t : ℝ) : (∫ x in S, (heatAt μ hQ t f x)^2 ∂μ) ≤ ‖f‖^2 := by
    have hi := setIntegral_le_integral (s := S) (Lp.memLp (heatAt μ hQ t f)).integrable_sq
      (Eventually.of_forall fun x => sq_nonneg (heatAt μ hQ t f x))
    rw [integral_sq_Lp] at hi
    have hn := (heatAt μ hQ t).le_of_opNorm_le (heatAt_norm_le μ hQ t) f
    simp only [one_mul] at hn
    exact hi.trans ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn)
  have hh := intervalIntegral.integral_mono_on hab
    (hc.intervalIntegrable (μ := volume) a b)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ‖f‖^2) volume a b)
    (fun t _ => ht t)
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh

theorem NoncollapsedRCD.heat_local_L2_smoothing {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
    letI : (hausdorff n X).Regular := inferInstance
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (x : X) (R τ : ℝ), 0 < R → -1 ≤ K*R^2 → 0 < τ →
      ∀ f : Lp ℝ 2 (hausdorff n X),
      ∀ᵐ y ∂(hausdorff n X).restrict (ball x (R/2)),
        |heatAt (hausdorff n X) hX.quadratic (τ+R^2) f y| ≤
          C/Real.sqrt ((hausdorff n X).real (ball x R))*‖f‖ := by
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let : (hausdorff n X).Regular := inferInstance
  obtain ⟨δ,hδ,hsmall⟩ := hX.heat_small_parabolic_mass_bound hn
  let C := 1+(Real.sqrt δ)⁻¹
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hC : 1 ≤ C := le_add_of_nonneg_right (inv_nonneg.mpr hsd.le)
  refine ⟨C,hC,?_⟩
  intro x R τ hR hcurv hτ f
  let μ := hausdorff n X
  let V := μ.real (ball x R)
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport x R hR).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hsv : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  by_cases hf : f = 0
  · subst f
    simp only [map_zero,norm_zero,mul_zero]
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_zero ℝ 2 μ)] with y hy
    rw [hy]
    simp only [Pi.zero_apply,abs_zero,le_refl]
  have hnf : 0 < ‖f‖ := norm_pos_iff.mpr hf
  let d := Real.sqrt δ*Real.sqrt V/‖f‖
  have hd : 0 < d := div_pos (mul_pos hsd hsv) hnf
  have hd2 : d^2*‖f‖^2 = δ*V := by
    dsimp only [d]
    rw [div_pow,mul_pow,Real.sq_sqrt hδ.le,Real.sq_sqrt hV.le]
    field_simp
  have hg : ‖d • f‖^2 = δ*V := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hd,mul_pow,hd2]
  have hbound (g : Lp ℝ 2 μ) (hg : ‖g‖^2 = δ*V) :
      ∀ᵐ y ∂μ.restrict (ball x (R/2)), heatAt μ hX.quadratic (τ+R^2) g y ≤ 1 := by
    apply hsmall x R τ hR hcurv hτ g
    have hh := heat_set_time_L2_bound μ hX.quadratic g (S := ball x R) measurableSet_ball
      (a := τ) (b := τ+R^2) (by linarith [sq_nonneg R])
    rw [hg] at hh
    nlinarith only [hh]
  have hup := hbound (d • f) hg
  have hdown := hbound (-(d • f)) (by simpa only [norm_neg] using hg)
  rw [map_smul] at hup
  rw [map_neg,map_smul] at hdown
  have hscale : 1 ≤ d*(C/Real.sqrt V*‖f‖) := by
    have heq : d*(C/Real.sqrt V*‖f‖) = Real.sqrt δ+1 := by
      dsimp only [d,C]
      field_simp
    rw [heq]
    linarith [Real.sqrt_nonneg δ]
  filter_upwards [hup,hdown,
    ae_restrict_of_ae (Lp.coeFn_smul d (heatAt μ hX.quadratic (τ+R^2) f)),
    ae_restrict_of_ae (Lp.coeFn_neg (d • heatAt μ hX.quadratic (τ+R^2) f))]
    with y hu hl hs hn
  simp only [Pi.smul_apply,smul_eq_mul] at hs
  simp only [Pi.neg_apply] at hn
  rw [hs] at hu
  rw [hn,hs] at hl
  have habs : d*|heatAt μ hX.quadratic (τ+R^2) f y| ≤ 1 := by
    have hh : |d*heatAt μ hX.quadratic (τ+R^2) f y| ≤ 1 := abs_le.mpr ⟨by linarith,hu⟩
    simpa only [abs_mul,abs_of_pos hd] using hh
  exact (mul_le_mul_iff_right₀ hd).mp (habs.trans hscale)

end RegularPointCoordinates

end

end OAI
