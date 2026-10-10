import OAI.Probability.FreeIsing.Posterior.ResponseTruncation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367

theorem tsum_capped_mul_error_sq_eq {ι : Type*} (C : ι → ℝ)
    {a : ℝ} (ha : a ≠ 0) (R : ℝ) :
    (∑' i, (a * C i - min a R * C i) ^ 2) =
      ((a - min a R) / a) ^ 2 * ∑' i, (a * C i) ^ 2 := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  field_simp

theorem tsum_capped_mul_error_sq_le_fourth {ι : Type*} (C : ι → ℝ)
    {a R K : ℝ} (ha : 1 ≤ a) (hR : 0 < R) (hK : 0 ≤ K)
    (hrow : (∑' i, (a * C i) ^ 2) ≤ K) :
    (∑' i, (a * C i - min a R * C i) ^ 2) ≤ K * a ^ 4 / R ^ 2 := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have hr : ((a - min a R) / a) ^ 2 ≤ (a - min a R) ^ 2 := by
    rw [div_pow]
    exact div_le_self (sq_nonneg _) ha2
  rw [tsum_capped_mul_error_sq_eq C ha0.ne' R]
  calc
    _ ≤ ((a - min a R) / a) ^ 2 * K :=
      mul_le_mul_of_nonneg_left hrow (sq_nonneg _)
    _ ≤ (a - min a R) ^ 2 * K := mul_le_mul_of_nonneg_right hr hK
    _ ≤ (a ^ 4 / R ^ 2) * K :=
      mul_le_mul_of_nonneg_right (sq_sub_min_le_fourth_div_sq ha0.le hR) hK
    _ = _ := by ring

theorem integral_capped_mul_error_row_le_fourth
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω] {P : Measure Ω}
    {A : Ω → ℝ} {C : ι → Ω → ℝ} {K R : ℝ}
    (hA : Measurable A) (hC : ∀ i, Measurable (C i))
    (hpos : ∀ᵐ ω ∂P, 1 ≤ A ω) (hK : 0 ≤ K) (hR : 0 < R)
    (hrow : ∀ᵐ ω ∂P, Summable (fun i => (A ω * C i ω) ^ 2) ∧
      (∑' i, (A ω * C i ω) ^ 2) ≤ K)
    (hfour : Integrable (fun ω => A ω ^ 4) P) :
    (∀ᵐ ω ∂P, Summable (fun i =>
      (A ω * C i ω - min (A ω) R * C i ω) ^ 2)) ∧
    Integrable (fun ω => ∑' i,
      (A ω * C i ω - min (A ω) R * C i ω) ^ 2) P ∧
    (∫ ω, ∑' i, (A ω * C i ω - min (A ω) R * C i ω) ^ 2 ∂P) ≤
      K * (∫ ω, A ω ^ 4 ∂P) / R ^ 2 := by
  have hb : ∀ᵐ ω ∂P,
      (∑' i, (A ω * C i ω - min (A ω) R * C i ω) ^ 2) ≤
        K * A ω ^ 4 / R ^ 2 := by
    filter_upwards [hpos, hrow] with ω hp hr
    exact tsum_capped_mul_error_sq_le_fourth (fun i => C i ω) hp hR hK hr.2
  have hi : Integrable (fun ω => ∑' i,
      (A ω * C i ω - min (A ω) R * C i ω) ^ 2) P := by
    apply ((hfour.const_mul K).div_const (R ^ 2)).mono'
      (Measurable.tsum (fun i => ((hA.mul (hC i)).sub
        ((hA.min measurable_const).mul (hC i))).pow_const 2)).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    simpa only [Pi.sub_apply, Pi.mul_apply, Real.norm_of_nonneg (tsum_nonneg (fun _ => sq_nonneg _))] using hω
  refine ⟨?_, hi, ?_⟩
  · filter_upwards [hpos, hrow] with ω hp hr
    exact (summable_capped_mul_error_sq (zero_le_one.trans hp) hR.le hr.1).1
  · calc
      _ ≤ ∫ ω, K * A ω ^ 4 / R ^ 2 ∂P :=
        integral_mono_ae hi ((hfour.const_mul K).div_const _) hb
      _ = _ := by rw [integral_div, integral_const_mul]

theorem HasFreeIsingLaw.cappedGibbsResponse_error_le_of_strict
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (u : TreeVertex d)
    {R : ℝ} (hR : 0 < R) :
    let Y := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
    let E := fun p => ∑' v,
      (infiniteGibbsResponse beta u v (Y p) - cappedGibbsResponse beta R u v (Y p)) ^ 2
    let K := 1 + (d : ℝ) * Real.tanh beta ^ 2 /
      (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2)
    Integrable E (μ.prod (Measure.infinitePi ν)) ∧
      (∫ p, E p ∂μ.prod (Measure.infinitePi ν)) ≤
        K * (2 * Real.exp (8 * ((d : ℝ) * beta + t) + (t : ℝ) * 8 ^ 2 / 2)) / R ^ 2 := by
  let Y := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
    fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
  let A := fun p => (1 - infiniteGibbsSpinMean beta u (Y p) ^ 2)⁻¹
  let C := fun v p => infiniteGibbsCovariance beta u v (Y p)
  let K := 1 + (d : ℝ) * Real.tanh beta ^ 2 /
    (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2)
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro i
    exact (measurable_const.mul ((measurable_of_finite spinSign).comp
      ((measurable_pi_apply i).comp measurable_fst))).add
      ((hmB i t).comp ((measurable_pi_apply i).comp measurable_snd))
  have hA : Measurable A :=
    (measurable_const.sub (((measurable_infiniteGibbsSpinMean beta u).comp hY).pow_const 2)).inv
  have hC (v : TreeVertex d) : Measurable (C v) :=
    (measurable_infiniteGibbsCovariance beta u v).comp hY
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hpos : ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), 1 ≤ A p := by
    filter_upwards [hμ.infiniteGibbsSpinMean_brownian_field_bound hbeta ν hB hmB t u]
      with p hp
    have hv : 0 < 1 - infiniteGibbsSpinMean beta u (Y p) ^ 2 := by
      dsimp only [Y]
      nlinarith [hp.1.1, hp.1.2]
    exact (one_le_inv₀ hv).mpr (by nlinarith [sq_nonneg (infiniteGibbsSpinMean beta u (Y p))])
  have hresp (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) (v : TreeVertex d) :
      A p * C v p = infiniteGibbsResponse beta u v (Y p) := by
    change (1 - infiniteGibbsSpinMean beta u (Y p) ^ 2)⁻¹ *
      infiniteGibbsCovariance beta u v (Y p) = _
    rw [infiniteGibbsResponse, div_eq_mul_inv, mul_comm]
  have hcap (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) (v : TreeVertex d) :
      min (A p) R * C v p = cappedGibbsResponse beta R u v (Y p) := rfl
  have hr := hμ.infiniteGibbsResponseRow_strict_bound_brownian hbeta hstrict ν hB hmB t u
  have hr' : ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      Summable (fun v => (A p * C v p) ^ 2) ∧ (∑' v, (A p * C v p) ^ 2) ≤ K := by
    filter_upwards [hr] with p hp
    simpa only [hresp] using (show Summable (fun v => infiniteGibbsResponse beta u v (Y p) ^ 2) ∧
      (∑' v, infiniteGibbsResponse beta u v (Y p) ^ 2) ≤ K from ⟨hp.1, hp.2.2⟩)
  have hf := hμ.brownian_gibbs_posterior_inverse_variance_moment hbeta ν hB hmB t u 4
  have he := integral_capped_mul_error_row_le_fourth hA hC hpos hK hR hr' hf.1
  have hb := he.2.2.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hf.2 hK) (sq_nonneg R))
  simp only [hresp, hcap] at he hb
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) * 4 = 8 by norm_num] at hb
  exact ⟨he.2.1, by simpa only [show (8 : ℝ) ^ 2 = 64 by norm_num] using hb⟩

theorem HasFreeIsingLaw.cappedGibbsResponse_time_error_le_of_strict
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i ω, Continuous (fun t => B i t ω))
    (T : ℝ≥0) (u : TreeVertex d) {R : ℝ} (hR : 0 < R) :
    let Y := fun p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      fun i => (p.1.toNNReal : ℝ) * spinSign (p.2.1 i) + B i p.1.toNNReal (p.2.2 i)
    let E := fun p => ∑' v,
      (infiniteGibbsResponse beta u v (Y p) - cappedGibbsResponse beta R u v (Y p)) ^ 2
    let K := 1 + (d : ℝ) * Real.tanh beta ^ 2 /
      (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2)
    let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    Integrable E P ∧ (∫ p, E p ∂P) ≤
      K * ((T : ℝ) * (2 * Real.exp (8 * ((d : ℝ) * beta + T) +
        (T : ℝ) * 8 ^ 2 / 2))) / R ^ 2 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let Y := fun p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
    fun i => (p.1.toNNReal : ℝ) * spinSign (p.2.1 i) + B i p.1.toNNReal (p.2.2 i)
  let K := 1 + (d : ℝ) * Real.tanh beta ^ 2 /
    (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro i
    have hBi : Measurable (Function.uncurry (B i)) :=
      measurable_uncurry_of_continuous_of_measurable (hcB i) (hmB i)
    exact ((measurable_coe_nnreal_real.comp (measurable_real_toNNReal.comp measurable_fst)).mul
      ((measurable_of_finite spinSign).comp
        ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))).add
      (hBi.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))))
  have hE : Measurable (fun p => ∑' v,
      (infiniteGibbsResponse beta u v (Y p) - cappedGibbsResponse beta R u v (Y p)) ^ 2) :=
    Measurable.tsum (fun v : TreeVertex d =>
    (((measurable_infiniteGibbsResponse beta u v).comp hY).sub
      ((measurable_cappedGibbsResponse beta R u v).comp hY)).pow_const 2)
  have h := integrable_prod_of_nonneg_section_bound
    (volume.restrict (Ioc (0 : ℝ) T)) (μ.prod (Measure.infinitePi ν))
    hE (fun _ => tsum_nonneg (fun _ => sq_nonneg _))
    (C := K * (2 * Real.exp (8 * ((d : ℝ) * beta + T) +
      (T : ℝ) * 8 ^ 2 / 2)) / R ^ 2) ?_ ?_
  · refine ⟨h.1, h.2.trans_eq ?_⟩
    rw [measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le T.coe_nonneg]
    dsimp only [K]
    ring
  · exact ae_of_all _ (fun t =>
      (hμ.cappedGibbsResponse_error_le_of_strict hbeta hstrict ν hB hmB t.toNNReal u hR).1)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hb := (hμ.cappedGibbsResponse_error_le_of_strict
      hbeta hstrict ν hB hmB t.toNNReal u hR).2
    apply hb.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg R)
    apply mul_le_mul_of_nonneg_left _ hK
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    have htT : (t.toNNReal : ℝ) ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
    nlinarith

end Problem367

end

end OAI
