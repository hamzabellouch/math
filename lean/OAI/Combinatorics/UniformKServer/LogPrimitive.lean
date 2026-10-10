import Mathlib
import OAI.Combinatorics.UniformKServer.Denominators

namespace OAI

namespace UniformKServer.LogPrimitive
open Set Filter MeasureTheory
open scoped Topology
noncomputable def primitive (D : ℝ → ℝ) (base scale S Q a : ℝ) : ℝ :=
  scale * ∫ s in base..a, (S-Q/s)/D s

def Contract (g D : ℝ → ℝ) (scale S Q : ℝ) : Prop :=
  ContinuousOn g (Icc 0 1) ∧
  (∀ a, 0 < a → a ≤ 1 → HasDerivAt g (scale*((S-Q/a)/D a)) a) ∧
  (0 < Q → 0 < scale → Tendsto (fun a => (g a-g 0)/a) (𝓝[>] 0) atBot)

-- CANDIDATE PROOFS

noncomputable def J (x : ℝ) : ℝ := if x = 0 then 0 else 1/(1+Real.log (1/x))
noncomputable def w (x : ℝ) : ℝ := 1/(x*(1+Real.log (1/x))^2)

theorem log_recip_top : Tendsto (fun x : ℝ => Real.log (1/x)) (𝓝[>] 0) atTop := by
  simpa only [one_div, Function.comp_def] using Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero

theorem J_continuous : ContinuousOn J (Icc 0 1) := by
  intro x hx
  by_cases hz : x = 0
  · subst x
    have ht : Tendsto J (𝓝[>] (0 : ℝ)) (𝓝 (J 0)) := by
      simp only [J]
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).add_atTop log_recip_top).inv_tendsto_atTop
      apply h.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp [J, ne_of_gt hx.out, one_div]
    exact (continuousWithinAt_Ioi_iff_Ici.mp ht).mono (fun x hx => hx.1)
  · have hp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hz)
    have hd : 1+Real.log (1/x) ≠ 0 := ne_of_gt (by
      linarith [UniformKServer.Denominators.log_nonneg hx.1 hx.2])
    apply ContinuousAt.continuousWithinAt
    apply ((continuousAt_const (y := (1 : ℝ))).div (continuousAt_const.add
      ((continuousAt_const.div continuousAt_id hz).log (one_div_ne_zero hz))) hd).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with y hy
    simp [J, hy]

theorem w_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ w x := by
  unfold w
  positivity

theorem J_derivative {x : ℝ} (hx : 0 < x) (hx₁ : x ≤ 1) : HasDerivAt J (w x) x := by
  have hd : 1+Real.log (1/x) ≠ 0 := ne_of_gt (by
    linarith [UniformKServer.Denominators.log_nonneg hx.le hx₁])
  have he : J =ᶠ[𝓝 x] (fun y : ℝ => (1+Real.log (1/y))⁻¹) := by
    filter_upwards [eventually_ne_nhds hx.ne'] with y hy
    simp [J, hy, one_div]
  apply HasDerivAt.congr_of_eventuallyEq _ he
  have hh := ((hasDerivAt_const x 1).add
    (((hasDerivAt_id x).inv hx.ne').log (inv_ne_zero hx.ne'))).inv (by simpa [one_div] using hd)
  convert! hh using 1
  · funext y; simp [one_div]
  · simp only [Pi.inv_apply, Pi.add_apply, id_eq, zero_add, one_div, w] at *
    field_simp [hx.ne', hd]

theorem w_integrable : IntervalIntegrable w volume 0 1 := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
  · simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using J_continuous
  · simp only [min_eq_left (by norm_num : (0 : ℝ) ≤ 1), max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    exact fun x hx => J_derivative hx.1 hx.2.le
  · simp only [min_eq_left (by norm_num : (0 : ℝ) ≤ 1), max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    exact fun x hx => w_nonneg hx.1.le

theorem integrand_integrable {D : ℝ → ℝ} (hDm : Measurable D) {c : ℝ} (hc : 0 < c)
    (hD : ∀ x, 0 < x → x ≤ 1 → c*(1+Real.log (1/x))^2 ≤ D x) (S Q : ℝ) :
    IntervalIntegrable (fun x => (S-Q/x)/D x) volume 0 1 := by
  apply (w_integrable.const_mul ((|S|+|Q|)/c)).mono_fun'
  · exact ((measurable_const.sub (measurable_const.div measurable_id)).div hDm).aestronglyMeasurable
  · rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hy : 0 ≤ Real.log (1/x) := UniformKServer.Denominators.log_nonneg hx.1.le hx.2
    have hq : 0 < (1+Real.log (1/x))^2 := sq_pos_of_pos (by linarith)
    have hDp : 0 < D x := lt_of_lt_of_le (mul_pos hc hq) (hD x hx.1 hx.2)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hDp]
    have hn : |S-Q/x| ≤ |S|+|Q|/x := by
      convert! abs_sub S (Q/x) using 1
      rw [abs_div, abs_of_pos hx.1]
    have hr : |S| * x+|Q| ≤ |S|+|Q| := by nlinarith [abs_nonneg S]
    calc
      _ ≤ (|S|+|Q|/x)/D x := div_le_div_of_nonneg_right hn hDp.le
      _ ≤ (|S|+|Q|/x)/(c*(1+Real.log (1/x))^2) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hc hq) (hD x hx.1 hx.2)
      _ = (|S| * x+|Q|)/(c*x*(1+Real.log (1/x))^2) := by field_simp [hx0.ne']
      _ ≤ (|S|+|Q|)/(c*x*(1+Real.log (1/x))^2) :=
        div_le_div_of_nonneg_right hr (by positivity)
      _ = ((|S|+|Q|)/c)*w x := by unfold w; simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem slope_atBot {f f' : ℝ → ℝ} (hfc : ContinuousOn f (Icc 0 1))
    (hfd : ∀ x, 0 < x → x ≤ 1 → HasDerivAt f (f' x) x)
    (hlim : Tendsto f' (𝓝[>] 0) atBot) :
    Tendsto (fun x => (f x-f 0)/x) (𝓝[>] 0) atBot := by
  apply tendsto_atBot.mpr
  intro K
  obtain ⟨δ, hδ, hb⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (hlim.eventually_le_atBot K)
  filter_upwards [Ioc_mem_nhdsGT (show 0 < min δ 1 by exact lt_min hδ (by norm_num))] with x hx
  obtain ⟨r, hr, he⟩ := exists_hasDerivAt_eq_slope f f' hx.1
    (hfc.mono (Icc_subset_Icc le_rfl (hx.2.trans (min_le_right _ _))))
    (fun r hr => hfd r hr.1 (hr.2.le.trans (hx.2.trans (min_le_right _ _))))
  have hk := hb (show r ∈ Ioc 0 δ from ⟨hr.1, hr.2.le.trans (hx.2.trans (min_le_left _ _))⟩)
  change f' r ≤ K at hk
  rw [he, sub_zero] at hk
  exact hk

theorem generic_contract {D : ℝ → ℝ} (hDm : Measurable D) {c : ℝ} (hc : 0 < c)
    (hD : ∀ x, 0 < x → x ≤ 1 → c*(1+Real.log (1/x))^2 ≤ D x)
    (hDc : ∀ x, 0 < x → x ≤ 1 → ContinuousAt D x)
    (hlim : Tendsto (fun x => x*D x) (𝓝[>] 0) (𝓝 0))
    (base scale S Q : ℝ) (hbase : base ∈ Icc 0 1) :
    Contract (primitive D base scale S Q) D scale S Q := by
  have hDp : ∀ x, 0 < x → x ≤ 1 → 0 < D x := by
    intro x hx hx₁
    have hy := UniformKServer.Denominators.log_nonneg hx.le hx₁
    exact lt_of_lt_of_le (mul_pos hc (sq_pos_of_pos (by linarith))) (hD x hx hx₁)
  let f := fun x => (S-Q/x)/D x
  have hfm : Measurable f := (measurable_const.sub (measurable_const.div measurable_id)).div hDm
  have hfi : IntervalIntegrable f volume 0 1 := integrand_integrable hDm hc hD S Q
  have hfba : ∀ a, a ∈ Icc (0 : ℝ) 1 → IntervalIntegrable f volume base a := by
    intro a ha
    apply hfi.mono_set
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact uIcc_subset_Icc hbase ha
  have hfc : ∀ a, 0 < a → a ≤ 1 → ContinuousAt f a := by
    intro a ha ha₁
    exact (continuousAt_const.sub (continuousAt_const.div continuousAt_id ha.ne')).div
      (hDc a ha ha₁) (hDp a ha ha₁).ne'
  have hg : ContinuousOn (primitive D base scale S Q) (Icc 0 1) := by
    have h₀ : IntegrableOn f (uIcc (0 : ℝ) 1) volume := (intervalIntegrable_iff' enorm_ne_top).mp hfi
    have h : ContinuousOn (fun a => ∫ x in 0..a, f x) (Icc (0 : ℝ) 1) := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        intervalIntegral.continuousOn_primitive_interval h₀
    have hh := h.sub (continuousOn_const (s := Icc (0 : ℝ) 1) (c := (∫ x in 0..base, f x)))
    apply (continuousOn_const.mul hh).congr
    intro a ha
    have h0a : IntervalIntegrable f volume 0 a := hfi.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact uIcc_subset_Icc (by simp) ha)
    have h0b : IntervalIntegrable f volume 0 base := (hfba 0 (by simp)).symm
    change scale*(∫ x in base..a, f x) = scale*((∫ x in 0..a, f x)-(∫ x in 0..base, f x))
    rw [intervalIntegral.integral_interval_sub_left h0a h0b]
  have hgd : ∀ a, 0 < a → a ≤ 1 → HasDerivAt (primitive D base scale S Q)
      (scale*((S-Q/a)/D a)) a := by
    intro a ha ha₁
    exact (intervalIntegral.integral_hasDerivAt_right (hfba a ⟨ha.le, ha₁⟩)
      hfm.stronglyMeasurable.stronglyMeasurableAtFilter (hfc a ha ha₁)).const_mul scale
  refine ⟨hg, hgd, ?_⟩
  intro hQ hs
  apply slope_atBot hg hgd
  have hden : Tendsto (fun x => x*D x) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hlim, ?_⟩
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
    exact mul_pos hx.1 (hDp x hx.1 hx.2)
  have hn : Tendsto (fun x : ℝ => S*x-Q) (𝓝[>] 0) (𝓝 (-Q)) := by
    have hx : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using ((tendsto_const_nhds (x := S)).mul hx).sub_const Q
  have hh := (Tendsto.neg_mul_atTop (neg_lt_zero.mpr hQ) hn hden.inv_tendsto_nhdsGT_zero) |> Tendsto.const_mul_atBot hs
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx.out
  dsimp only [Pi.inv_apply]
  field_simp [hx0]

theorem powlog_zero (n : ℕ) :
    Tendsto (fun x : ℝ => x*(Real.log (1/x))^n) (𝓝[>] 0) (𝓝 0) := by
  simpa only [Function.comp_def, one_mul, mul_one, add_zero, div_inv_eq_mul, one_div, mul_comm] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero).comp tendsto_inv_nhdsGT_zero

theorem log_recip_continuousAt {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt (fun x : ℝ => Real.log (1/x)) x :=
  (continuousAt_const.div continuousAt_id hx).log (one_div_ne_zero hx)

open UniformKServer.Denominators

theorem regular_lower {h x : ℝ} (hh : 1 ≤ h) (hx : 0 < x) (hx₁ : x ≤ 1) :
    (1/h)*(1+Real.log (1/x))^2 ≤ regular h x := by
  have hp : 0 < h := by linarith
  have hy := log_nonneg hx.le hx₁
  unfold regular
  rw [one_div, ← div_eq_inv_mul]
  apply (div_le_div_iff_of_pos_right hp).mpr
  nlinarith

theorem marked_lower {u x : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (hx : 0 < x) (hx₁ : x ≤ 1) :
    (u/4)*(1+Real.log (1/x))^2 ≤ marked u x := by
  have hH := height_ge_one hu hu₁
  have hy := log_nonneg hx.le hx₁
  have h₁ := mul_le_mul_of_nonneg_right hu₁ hy
  have h₂ := mul_le_mul_of_nonneg_right hu₁ (sq_nonneg (Real.log (1/x)))
  have h₃ := mul_le_mul_of_nonneg_right hH hy
  have h₄ := mul_le_mul_of_nonneg_right hH (sq_nonneg (Real.log (1/x)))
  unfold marked
  nlinarith

theorem regular_contract (h scale S Q : ℝ) (hh : 1 ≤ h) :
    Contract (primitive (regular h) 0 scale S Q) (regular h) scale S Q := by
  have hp : 0 < h := by linarith
  apply generic_contract (c := 1/h)
  · unfold regular
    fun_prop
  · positivity
  · exact fun x hx hx₁ => regular_lower hh hx hx₁
  · intro x hx hx₁
    unfold regular
    exact (continuousAt_const.add (log_recip_continuousAt hx.ne')).pow 2 |>.div_const h
  · have hx : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hy : Tendsto (fun x : ℝ => x*Real.log (1/x)) (𝓝[>] 0) (𝓝 0) := by simpa using powlog_zero 1
    have ht := ((hx.const_mul h).add (hy.const_mul 2)).add ((powlog_zero 2).div_const h)
    simp only [mul_zero, zero_add, zero_div] at ht
    apply ht.congr'
    exact Filter.Eventually.of_forall fun x => by unfold regular; field_simp; ring
  · simp

theorem marked_contract (u scale S Q : ℝ) (hu : 0 < u) (hu₁ : u ≤ 1) :
    Contract (primitive (marked u) 1 scale S Q) (marked u) scale S Q := by
  apply generic_contract (c := u/4)
  · unfold marked
    fun_prop
  · positivity
  · exact fun x hx hx₁ => marked_lower hu hu₁ hx hx₁
  · intro x hx hx₁
    unfold marked
    have hl := log_recip_continuousAt hx.ne'
    exact continuousAt_const.add ((continuousAt_const.mul hl).mul (continuousAt_const.add hl))
  · have hx : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hy : Tendsto (fun x : ℝ => x*Real.log (1/x)) (𝓝[>] 0) (𝓝 0) := by simpa using powlog_zero 1
    have ht := ((hx.const_mul u).add (hy.const_mul (height u))).add ((powlog_zero 2).const_mul (height u))
    simp only [mul_zero, zero_add] at ht
    apply ht.congr'
    exact Filter.Eventually.of_forall fun x => by unfold marked; ring
  · simp

end UniformKServer.LogPrimitive


                                                                             
                                                                               
                                                                         
                                                                               


end OAI
