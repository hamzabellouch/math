import OAI.Geometry.RCD.Harmonic.L2ProbabilityPairing
import OAI.Geometry.RCD.Heat.KernelHeatL2Representation

namespace OAI

/-! # Heat mean errors at shrinking physical and volume scales -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MeasurableSpace X]

theorem normalized_l2_probability_pairing (μ : Measure X)
    (r m : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hm : ∀ k, 0 < m k)
    (ν : ℕ → Y → Measure X) [∀ k y, IsProbabilityMeasure (ν k y)]
    {C : ℝ} (hC : 0 ≤ C)
    (hν : ∀ k y, ν k y ≤ ENNReal.ofReal (C/m k) • μ)
    (F f : ℕ → Lp ℝ 2 μ)
    (hF : Tendsto (fun k => ‖F k-f k‖/(r k*Real.sqrt (m k))) atTop (𝓝 0)) :
    TendstoUniformly (fun k y => ((∫ x, F k x ∂ν k y)-(∫ x, f k x ∂ν k y))/r k)
      (fun _ => 0) atTop := by
  have hn : Tendsto (fun k => Real.sqrt C*(‖F k-f k‖/(r k*Real.sqrt (m k))))
      atTop (𝓝 0) := by simpa only [mul_zero] using hF.const_mul (Real.sqrt C)
  apply Metric.tendstoUniformly_iff.mpr
  intro e he
  filter_upwards [(tendsto_order.mp hn).2 e he] with k hk y
  have hi (g : Lp ℝ 2 μ) : Integrable g (ν k y) :=
    (((Lp.memLp g).of_measure_le_smul ENNReal.ofReal_ne_top (hν k y)).mono_exponent
      (by norm_num : (1:ℝ≥0∞) ≤ 2)).integrable (by norm_num)
  have hbound := integral_abs_le_l2_of_domination μ (ν k y) ENNReal.ofReal_ne_top
    (hν k y) (fun x => (F k-f k : Lp ℝ 2 μ) x) (Lp.memLp (F k-f k))
  have hae : F k-f k =ᵐ[ν k y] fun x => F k x-f k x :=
    (Measure.absolutelyContinuous_of_le_smul (hν k y)).ae_eq (Lp.coeFn_sub (F k) (f k))
  have heq : (∫ x, |(F k-f k : Lp ℝ 2 μ) x| ∂ν k y)=∫ x, |F k x-f k x| ∂ν k y :=
    integral_congr_ae (by filter_upwards [hae] with x hx; rw [hx])
  have hcoef : (ENNReal.ofReal (C/m k)^(1/2:ℝ)).toReal=Real.sqrt C/Real.sqrt (m k) := by
    rw [← ENNReal.toReal_rpow,ENNReal.toReal_ofReal (div_nonneg hC (hm k).le),
      ← Real.sqrt_eq_rpow,Real.sqrt_div hC]
  rw [heq,hcoef] at hbound
  change (∫ x, |F k x-f k x| ∂ν k y) ≤ Real.sqrt C/Real.sqrt (m k)*‖F k-f k‖ at hbound
  have habs := abs_integral_le_integral_abs (f := fun x => F k x-f k x) (μ := ν k y)
  rw [integral_sub (hi (F k)) (hi (f k))] at habs
  have hfinal : |((∫ x, F k x ∂ν k y)-(∫ x, f k x ∂ν k y))/r k| ≤
      Real.sqrt C*(‖F k-f k‖/(r k*Real.sqrt (m k))) := by
    rw [abs_div,abs_of_pos (hr k)]
    apply (div_le_div_of_nonneg_right (habs.trans hbound) (hr k).le).trans_eq
    ring
  simpa only [dist_zero_left,Real.norm_eq_abs] using hfinal.trans_lt hk

end RegularPointCoordinates

namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)

theorem normalized_heat_means_limit {ker : ℕ → ℝ → X → X → ℝ}
    (hk : ∀ k, IsContinuousHeatKernel μ Q (ker k))
    (r m : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hm : ∀ k, 0 < m k)
    (ν : ℕ → Y → Measure X) [∀ k y, IsProbabilityMeasure (ν k y)]
    {C : ℝ} (hC : 0 ≤ C)
    (hν : ∀ k y, ν k y ≤ ENNReal.ofReal (C/m k) • μ)
    (u : ℕ → SobolevSpace μ Q) (U : ℕ → X → ℝ)
    (hU : ∀ k, SobolevSpace.toLp μ Q (u k) =ᵐ[μ] U k)
    (s : ℕ → ℝ) (hs : ∀ k, 0 < s k)
    (hval : Tendsto (fun k =>
      ‖heatSobolev μ Q (s k) (hs k) (SobolevSpace.toLp μ Q (u k))-u k‖/
        (r k*Real.sqrt (m k))) atTop (𝓝 0)) :
    TendstoUniformly (fun k y =>
      ((∫ x, kernelHeat μ Q (hk k) (s k) (SobolevSpace.toLp μ Q (u k)) x ∂ν k y)-
        (∫ x, U k x ∂ν k y))/r k) (fun _ => 0) atTop := by
  have hnorm : Tendsto (fun k =>
      ‖heatAt μ Q (s k) (SobolevSpace.toLp μ Q (u k))-SobolevSpace.toLp μ Q (u k)‖/
        (r k*Real.sqrt (m k))) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => div_nonneg (norm_nonneg _)
      (mul_pos (hr k) (Real.sqrt_pos.mpr (hm k))).le) _ hval
    intro k
    apply div_le_div_of_nonneg_right _ (mul_pos (hr k) (Real.sqrt_pos.mpr (hm k))).le
    simpa only [map_sub,heatSobolev_toLp] using
      SobolevSpace.norm_toLp_le μ Q
        (heatSobolev μ Q (s k) (hs k) (SobolevSpace.toLp μ Q (u k))-u k)
  have hlim := normalized_l2_probability_pairing μ r m hr hm ν hC hν
    (fun k => heatAt μ Q (s k) (SobolevSpace.toLp μ Q (u k)))
    (fun k => SobolevSpace.toLp μ Q (u k)) hnorm
  have hheat (k : ℕ) (y : Y) :
      (∫ x, kernelHeat μ Q (hk k) (s k) (SobolevSpace.toLp μ Q (u k)) x ∂ν k y)=
        ∫ x, heatAt μ Q (s k) (SobolevSpace.toLp μ Q (u k)) x ∂ν k y :=
    integral_congr_ae ((Measure.absolutelyContinuous_of_le_smul (hν k y)).ae_eq
      (kernelHeat_represents_L2 μ Q (hk k) (hs k) _))
  have horig (k : ℕ) (y : Y) :
      (∫ x, U k x ∂ν k y)=∫ x, SobolevSpace.toLp μ Q (u k) x ∂ν k y :=
    integral_congr_ae ((Measure.absolutelyContinuous_of_le_smul (hν k y)).ae_eq (hU k).symm)
  simpa only [hheat,horig] using hlim

end RegularPointCoordinates

end

end OAI
