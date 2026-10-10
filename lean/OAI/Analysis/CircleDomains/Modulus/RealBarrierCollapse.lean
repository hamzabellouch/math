import OAI.Analysis.CircleDomains.Modulus.RealBarrierVanishing
import OAI.Analysis.CircleDomains.Selection.VerticalRealSequence
import OAI.Analysis.CircleDomains.Selection.VerticalRealRetention
import OAI.Analysis.CircleDomains.Modulus.FiniteCircleBarrierCollapse

namespace OAI

/-! Vanishing retained real barriers collapse compact target continua. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem RealModelExhaustion.real_projection_payment
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    (M : RealModelExhaustion d O ε)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0))
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
      finiteCoord ((M.stages (r n)).forward (z : Sphere))) F
      atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    {l : ℕ} (B : RetainedRealBarrier d F l)
    {C : Set ℂ} (hC : IsCompact C) (hCB : C ⊆ jordanInterior B.target_inner)
    {L : ℝ} (hL : 3 * M.radius ≤ L)
    (hBL : closure (jordanInterior B.target_outer) ⊆ ball 0 L) :
    (volume (Complex.re '' C)).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
        (∫ x in realChartDomain G,
          gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      2 * L * Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) := by
  apply M.limiting_vertical_line_payment hsard hsch harea hε r hr l hL
    (hC.image Complex.continuous_re).measurableSet
  exact M.eventually_vertical_test_crossings hsch hG r hr F hF hlim B.inner B.outer
    B.inner_index B.outer_index l B.value_one B.value_zero B.target_inner B.target_outer
    B.inner_image B.outer_image B.inner_side B.outer_side B.nested hC hCB hBL

theorem RealModelExhaustion.real_projection_zero_of_vanishing_barriers
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    (M : RealModelExhaustion d O ε)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0))
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
      finiteCoord ((M.stages (r n)).forward (z : Sphere))) F
      atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (labels : ℕ → ℕ) (B : ∀ k, RetainedRealBarrier d F (labels k))
    {C : Set ℂ} (hC : IsCompact C)
    (hCB : ∀ k, C ⊆ jordanInterior (B k).target_inner)
    {L : ℝ} (hL : 3 * M.radius ≤ L)
    (hBL : ∀ k, closure (jordanInterior (B k).target_outer) ⊆ ball 0 L)
    (hsmall : Tendsto (fun k =>
      Real.sqrt (∫ x in realChartDomain G,
        gradientEnergy (d.physical (labels k)) (fun z => sphericalMetricFactor z • 1) x) +
      Real.sqrt (∑' s, (d.upper (labels k) s - d.lower (labels k) s) ^ 2))
      atTop (𝓝 0)) : volume (Complex.re '' C) = 0 := by
  have hL0 : 0 ≤ L := (mul_nonneg (by norm_num) M.radius_pos.le).trans hL
  have hpay (k : ℕ) := M.real_projection_payment hsard hsch harea hG hε r hr F hF hlim
    (B k) hC (hCB k) hL (hBL k)
  have hbound : ∀ k, (volume (Complex.re '' C)).toReal ≤
      ((Real.sqrt Real.pi + 2) * L) *
        (Real.sqrt (∫ x in realChartDomain G,
          gradientEnergy (d.physical (labels k)) (fun z => sphericalMetricFactor z • 1) x) +
        Real.sqrt (∑' s, (d.upper (labels k) s - d.lower (labels k) s) ^ 2)) := by
    intro k
    apply (hpay k).trans
    have ha := Real.sqrt_nonneg (∫ x in realChartDomain G,
      gradientEnergy (d.physical (labels k)) (fun z => sphericalMetricFactor z • 1) x)
    have hb := Real.sqrt_nonneg (∑' s, (d.upper (labels k) s - d.lower (labels k) s) ^ 2)
    have hp := Real.sqrt_nonneg Real.pi
    nlinarith [mul_nonneg hL0 ha, mul_nonneg hL0 hb, mul_nonneg hp (mul_nonneg hL0 hb)]
  have hz : (volume (Complex.re '' C)).toReal = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    have ht := hsmall.const_mul ((Real.sqrt Real.pi + 2) * L)
    rw [mul_zero] at ht
    exact ge_of_tendsto ht (Eventually.of_forall hbound)
  have hfinite : volume (Complex.re '' C) ≠ ⊤ :=
    (hC.image Complex.continuous_re).measure_ne_top
  simpa only [ENNReal.toReal_eq_zero_iff, hfinite, or_false] using hz

theorem RealModelExhaustion.subsingleton_of_vanishing_barriers
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    (M : RealModelExhaustion d O ε)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0))
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
      finiteCoord ((M.stages (r n)).forward (z : Sphere))) F
      atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (labels : ℕ → ℕ) (B : ∀ k, RetainedRealBarrier d F (labels k))
    {C : Set ℂ} (hC : IsCompact C) (hconn : IsConnected C)
    (hCB : ∀ k, C ⊆ jordanInterior (B k).target_inner)
    {L : ℝ} (hL : 3 * M.radius ≤ L)
    (hBL : ∀ k, closure (jordanInterior (B k).target_outer) ⊆ ball 0 L)
    (hsmall : Tendsto (fun k =>
      Real.sqrt (∫ x in realChartDomain G,
        gradientEnergy (d.physical (labels k)) (fun z => sphericalMetricFactor z • 1) x) +
      Real.sqrt (∑' s, (d.upper (labels k) s - d.lower (labels k) s) ^ 2))
      atTop (𝓝 0)) : C.Subsingleton :=
  subsingleton_of_zero_projection_measure hC hconn
    (M.real_projection_zero_of_vanishing_barriers hsard hsch harea hG hε
      r hr F hF hlim labels B hC hCB hL hBL hsmall)
    (M.projection_zero_of_vanishing_barriers hsard hsch harea hG hε
      r hr F hF hlim labels B hC hCB hL hBL hsmall)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
