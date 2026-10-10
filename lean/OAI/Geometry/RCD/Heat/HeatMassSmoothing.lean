import OAI.Geometry.RCD.Heat.HeatLocalSmoothing

namespace OAI

/-! # Local heat smoothing with the cylinder mass retained -/

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heat_set_time_smul_square (f : Lp ℝ 2 μ) (d : ℝ) {S : Set X}
    (_hS : MeasurableSet S) (a b : ℝ) :
    (∫ t in a..b, ∫ x in S, (heatAt μ hQ t (d • f) x)^2 ∂μ) =
      d^2*(∫ t in a..b, ∫ x in S, (heatAt μ hQ t f x)^2 ∂μ) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  change (∫ x in S, (heatAt μ hQ t (d • f) x)^2 ∂μ) =
    d^2*(∫ x in S, (heatAt μ hQ t f x)^2 ∂μ)
  rw [map_smul,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul d (heatAt μ hQ t f))] with x hx
  simp only [Pi.smul_apply,smul_eq_mul] at hx
  rw [hx,mul_pow]

theorem NoncollapsedRCD.heat_cylinder_L2_smoothing {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
    letI : (hausdorff n X).Regular := inferInstance
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (x : X) (R τ M : ℝ), 0 < R → -1 ≤ K*R^2 → 0 < τ → 0 < M →
      ∀ f : Lp ℝ 2 (hausdorff n X),
      (∫ t in τ..(τ+R^2), ∫ y in ball x R, (heatAt (hausdorff n X) hX.quadratic t f y)^2
        ∂hausdorff n X) ≤ R^2*M^2 →
      ∀ᵐ y ∂(hausdorff n X).restrict (ball x (R/2)),
        |heatAt (hausdorff n X) hX.quadratic (τ+R^2) f y| ≤
          C/Real.sqrt ((hausdorff n X).real (ball x R))*M := by
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let : (hausdorff n X).Regular := inferInstance
  obtain ⟨δ,hδ,hsmall⟩ := hX.heat_small_parabolic_mass_bound hn
  let C := 1+(Real.sqrt δ)⁻¹
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  refine ⟨C,le_add_of_nonneg_right (inv_nonneg.mpr hsd.le),?_⟩
  intro x R τ M hR hcurv hτ hM f hmass
  let μ := hausdorff n X
  let V := μ.real (ball x R)
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport x R hR).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hsv : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  let d := Real.sqrt δ*Real.sqrt V/M
  have hd : 0 < d := div_pos (mul_pos hsd hsv) hM
  have hd2 : d^2*M^2 = δ*V := by
    dsimp only [d]
    rw [div_pow,mul_pow,Real.sq_sqrt hδ.le,Real.sq_sqrt hV.le]
    field_simp
  have hbound (c : ℝ) (hc : c^2 = d^2) :
      ∀ᵐ y ∂μ.restrict (ball x (R/2)), heatAt μ hX.quadratic (τ+R^2) (c • f) y ≤ 1 := by
    apply hsmall x R τ hR hcurv hτ (c • f)
    rw [heat_set_time_smul_square μ hX.quadratic f c measurableSet_ball, hc]
    calc
      _ ≤ d^2*(R^2*M^2) := mul_le_mul_of_nonneg_left hmass (sq_nonneg d)
      _ = δ*(R^2*V) := by nlinarith only [hd2]
  have hup := hbound d rfl
  have hdown := hbound (-d) (neg_sq d)
  rw [map_smul] at hup hdown
  have hscale : 1 ≤ d*(C/Real.sqrt V*M) := by
    have heq : d*(C/Real.sqrt V*M) = Real.sqrt δ+1 := by
      dsimp only [d,C]
      field_simp
    rw [heq]
    linarith [Real.sqrt_nonneg δ]
  filter_upwards [hup,hdown,
    ae_restrict_of_ae (Lp.coeFn_smul d (heatAt μ hX.quadratic (τ+R^2) f)),
    ae_restrict_of_ae (Lp.coeFn_smul (-d) (heatAt μ hX.quadratic (τ+R^2) f))]
    with y hu hl hs hn
  simp only [Pi.smul_apply,smul_eq_mul] at hs hn
  rw [hs] at hu
  rw [hn] at hl
  have habs : d*|heatAt μ hX.quadratic (τ+R^2) f y| ≤ 1 := by
    have hh : |d*heatAt μ hX.quadratic (τ+R^2) f y| ≤ 1 := abs_le.mpr ⟨by nlinarith,hu⟩
    simpa only [abs_mul,abs_of_pos hd] using hh
  exact (mul_le_mul_iff_right₀ hd).mp (habs.trans hscale)

end RegularPointCoordinates

end

end OAI
