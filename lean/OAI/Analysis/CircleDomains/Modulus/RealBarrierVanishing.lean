import OAI.Analysis.CircleDomains.Modulus.RealBarrierProjection

namespace OAI

/-! Vanishing source barrier norms force a zero-length target projection. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem RealModelExhaustion.projection_zero_of_vanishing_barriers
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
      atTop (𝓝 0)) : volume (Complex.im '' C) = 0 := by
  have hL0 : 0 ≤ L := (mul_nonneg (by norm_num) M.radius_pos.le).trans hL
  have hpay (k : ℕ) := M.projection_payment hsard hsch harea hG hε r hr F hF hlim
    (B k) hC (hCB k) hL (hBL k)
  have hbound : ∀ k, (volume (Complex.im '' C)).toReal ≤
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
  have hz : (volume (Complex.im '' C)).toReal = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    have ht := hsmall.const_mul ((Real.sqrt Real.pi + 2) * L)
    rw [mul_zero] at ht
    exact ge_of_tendsto ht (Eventually.of_forall hbound)
  have hfinite : volume (Complex.im '' C) ≠ ⊤ :=
    (hC.image Complex.continuous_im).measure_ne_top
  simpa only [ENNReal.toReal_eq_zero_iff, hfinite, or_false] using hz

end CircleDomainRigidity.FiniteTransfer

end

end OAI
