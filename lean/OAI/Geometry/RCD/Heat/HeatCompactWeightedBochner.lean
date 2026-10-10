import OAI.Geometry.RCD.Heat.KernelHeatGeneratorBochner

namespace OAI

/-! # Compact weighted dimensional heat estimate

The actual generator term is retained while the output local slope is
replaced by the minimal relaxed gradient. Compact initial slope majorants
are sufficient for the Sobolev recovery step.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_compact_weighted_generator_bochner
    (K : ℝ) (n : ℕ) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N)
    {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (f G w : Lp ℝ 2 (hausdorff n X))
    (hf : φ =ᵐ[hausdorff n X] f) (hG : IsSlopeMajorant (hausdorff n X) φ G)
    (hw : 0 ≤ w) (C : ℝ≥0) (hwC : ∀ᵐ x ∂hausdorff n X, |w x| ≤ C) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ {t : ℝ} (ht : 0 < t),
      (∫ x, w x*(SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic t ht f) x)^2 ∂hausdorff n X)+
      (2*t/N)*(∫ x, w x*((-heatGeneratorAt (hausdorff n X) hX.quadratic t f) x)^2 ∂hausdorff n X) ≤
      Real.exp (-2*K*t)*(∫ x, heatAt (hausdorff n X) hX.quadratic t w x*(G x)^2 ∂hausdorff n X) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro t ht
  obtain ⟨R,hR⟩ := hs.isCompact.isBounded.subset_closedBall p
  have hsupp (x : X) (hx : R < dist p x) : φ x = 0 := by
    by_contra hh
    have h := hR (subset_tsupport φ hh)
    simp only [mem_closedBall,dist_comm] at h
    linarith
  let hm := localSlope_sq_compact_memLp μ hφ p R hsupp
  let H := hm.toLp (fun x => (localSlope φ x).toReal^2)
  have hH : ⇑H =ᵐ[μ] fun x => (localSlope φ x).toReal^2 := hm.coeFn_toLp
  have hHi : Integrable H μ :=
    (localSlope_toReal_memLp μ hφ (slopeEnergy_lt_top_of_lipschitz_hasCompactSupport μ hφ hs).ne).integrable_sq.congr hH.symm
  obtain ⟨V,hV,heV,hgrad⟩ := hX.heat_lipschitz_gradient_compact K n hn hφ p R hsupp f H hf hH.symm ht.le
  let D := -heatGeneratorAt μ hX.quadratic t f
  have hVe : V = kernelHeat μ hX.quadratic hk t f := by
    let := hX.openPos K n
    exact MeasureTheory.Measure.eq_of_ae_eq
      (heV.symm.trans (kernelHeat_represents_L2 μ hX.quadratic hk ht f).symm)
      hV.continuous (kernelHeat_continuous μ hX.quadratic hk ht f)
  have hfull : ∀ᵐ x ∂μ, (localSlope V x).toReal^2+(2*t/N)*(D x)^2 ≤
      Real.exp (-2*K*t)*heatAt μ hX.quadratic t H x := by
    filter_upwards [kernelHeatGeneratorSource_represents μ hX.quadratic hk ht f,
      kernelHeat_represents_L2 μ hX.quadratic hk ht H,
      Lp.coeFn_neg (heatGeneratorAt μ hX.quadratic t f)] with x hd hh hneg
    have hb := hX.kernel_heat_local_generator_bochner K n hn hK hN hk f hφ p R hsupp hf H hH.symm ht x
    change (localSlope (kernelHeat μ hX.quadratic hk t f) x).toReal^2+
      (2*t/N)*(kernelHeatGeneratorSource μ hX.quadratic hk t f x)^2 ≤
        Real.exp (-2*K*t)*kernelHeat μ hX.quadratic hk t H x at hb
    rw [← hVe,hd,hh] at hb
    simpa only [Pi.neg_apply,← hneg] using hb
  have hPH := heatAt_integrable μ hX.quadratic t H hHi
  have hVsq : Integrable (fun x => (localSlope V x).toReal^2) μ := by
    apply (hPH.const_mul (Real.exp (-2*K*t))).mono'
      ((localSlope_measurable hV.continuous).ennreal_toReal.pow_const 2).aestronglyMeasurable
    filter_upwards [hgrad] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ((localSlope V x).toReal))] using hx
  have hVm : MemLp (fun x => (localSlope V x).toReal) 2 μ :=
    (memLp_two_iff_integrable_sq ((localSlope_measurable hV.continuous).ennreal_toReal.aestronglyMeasurable)).mpr hVsq
  let S := SobolevSpace.minimalSlope μ hX.quadratic (heatSobolev μ hX.quadratic t ht f)
  have hSle := SobolevSpace.minimalSlope_le_localSlope μ hX.quadratic
    (heatSobolev μ hX.quadratic t ht f) hV heV hVm
  have hS0 := (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hX.quadratic
    (heatSobolev μ hX.quadratic t ht f))
  have hw0 := (Lp.coeFn_nonneg _).mpr hw
  have hwb : ∀ᵐ x ∂μ, ‖w x‖ ≤ (C:ℝ) := by simpa only [Real.norm_eq_abs] using hwC
  have hPwb : ∀ᵐ x ∂μ, ‖heatAt μ hX.quadratic t w x‖ ≤ (C:ℝ) := by
    simpa only [Real.norm_eq_abs] using heatAt_abs_le_const μ hX.quadratic t C w hwC
  have hPw0 := (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hX.quadratic t w hw)
  have hpair : (∫ x, w x*heatAt μ hX.quadratic t H x ∂μ) =
      ∫ x, heatAt μ hX.quadratic t w x*(localSlope φ x).toReal^2 ∂μ := by
    have he := heatAt_inner μ hX.quadratic t w H
    simp only [L2.inner_def,Real.inner_apply] at he
    rw [← he]
    apply integral_congr_ae
    filter_upwards [hH] with x hx
    rw [hx]
  have hiS := (Lp.memLp S).integrable_sq.bdd_mul (Lp.aestronglyMeasurable w) hwb
  have hiD := (Lp.memLp D).integrable_sq.bdd_mul (Lp.aestronglyMeasurable w) hwb
  calc
    (∫ x, w x*(S x)^2 ∂μ)+(2*t/N)*(∫ x, w x*(D x)^2 ∂μ) =
        ∫ x, w x*((S x)^2+(2*t/N)*(D x)^2) ∂μ := by
      rw [← integral_const_mul,← integral_add hiS (hiD.const_mul (2*t/N))]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ ≤ ∫ x, w x*(Real.exp (-2*K*t)*heatAt μ hX.quadratic t H x) ∂μ := by
      apply integral_mono_ae ((hiS.add (hiD.const_mul (2*t/N))).congr
        (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring))
        ((hPH.const_mul _).bdd_mul (Lp.aestronglyMeasurable w) hwb)
      filter_upwards [hw0,hS0,hSle,hfull] with x hw hs hsle hg
      apply mul_le_mul_of_nonneg_left _ hw
      exact (add_le_add (pow_le_pow_left₀ hs hsle 2) le_rfl).trans hg
    _ = Real.exp (-2*K*t)*(∫ x, heatAt μ hX.quadratic t w x*(localSlope φ x).toReal^2 ∂μ) := by
      simp_rw [mul_left_comm (w _) (Real.exp (-2*K*t))]
      rw [integral_const_mul,hpair]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply integral_mono_ae
        (((localSlope_toReal_memLp μ hφ (slopeEnergy_lt_top_of_lipschitz_hasCompactSupport μ hφ hs).ne).integrable_sq).bdd_mul
          (Lp.aestronglyMeasurable _) hPwb)
        ((Lp.memLp G).integrable_sq.bdd_mul (Lp.aestronglyMeasurable _) hPwb)
      filter_upwards [hPw0,hG] with x hw hG
      apply mul_le_mul_of_nonneg_left _ hw
      apply pow_le_pow_left₀ ENNReal.toReal_nonneg _ 2
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hG.2
      simpa only [ENNReal.toReal_ofReal hG.1] using hh


end RegularPointCoordinates

end

end OAI
