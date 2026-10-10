import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Basic

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings

theorem secant_lower_bound
    {h : ℝ → ℝ} {d : ℝ}
    (hdiff : ∀ x > 0, DifferentiableAt ℝ h x)
    (hineq : ∀ x > 0, h x - 1 ≤ x * deriv h x)
    (hlim : Tendsto (fun x => (h x - 1) / x) (𝓝[>] (0 : ℝ)) (𝓝 d))
    {a : ℝ} (ha : 0 < a) : 1 + d * a ≤ h a := by
  let f : ℝ → ℝ := fun x => (h x - 1) / x
  have hfderiv : ∀ x > 0,
      HasDerivAt f ((deriv h x * x - (h x - 1)) / x ^ 2) x := by
    intro x hx
    convert
      (((hdiff x hx).hasDerivAt.sub_const 1).div (hasDerivAt_id x) (ne_of_gt hx)) using 1 <;>
        first | rfl | simp
  have hfmono : MonotoneOn f (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro x hx
      exact (hfderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hfderiv x (by simpa using hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : 0 < x := by simpa using hx
      rw [(hfderiv x hx').deriv]
      apply div_nonneg _ (sq_nonneg x)
      have := hineq x hx'
      nlinarith
  have hb : d ≤ f a := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with x hx hxa
    exact hfmono hx ha (le_of_lt hxa)
  dsimp [f] at hb
  have := (le_div_iff₀ ha).mp hb
  linarith

theorem chord_scalar_bound
    {J G : ℝ → ℝ} {q D : ℝ} (hq : 0 < q) (hD : 0 ≤ D)
    (hG0 : G 0 = 1)
    (hGderiv0 : HasDerivWithinAt G (-q * D) (Ici 0) 0)
    (hGpos : ∀ a > 0, 0 < G a)
    (hJnonneg : ∀ a > 0, 0 ≤ J a)
    (hGdiff : ∀ a > 0, DifferentiableAt ℝ G a)
    (hJle : ∀ a > 0, J a ^ (q / (q + 1)) ≤ G a)
    (hODE : ∀ a > 0, a * deriv G a = q * (J a - G a))
    {a : ℝ} (ha : 0 < a) : J a ≤ (1 + D * a) ^ (-(q + 1)) := by
  let h : ℝ → ℝ := fun x => G x ^ (-1 / q)
  have hqp : 0 < q + 1 := by linarith
  have hGI {x : ℝ} (hx : 0 < x) :
      J x * G x ^ (-((q + 1) / q)) ≤ 1 := by
    have hj : J x ≤ G x ^ ((q + 1) / q) := by
      have ht := Real.rpow_le_rpow (Real.rpow_nonneg (hJnonneg x hx) _)
        (hJle x hx) (le_of_lt (div_pos hqp hq))
      rw [← Real.rpow_mul (hJnonneg x hx)] at ht
      have he : q / (q + 1) * ((q + 1) / q) = 1 := by
        field_simp
      simpa [he] using ht
    rw [Real.rpow_neg (le_of_lt (hGpos x hx))]
    exact (mul_inv_le_iff₀ (Real.rpow_pos_of_pos (hGpos x hx) _)).mpr (by simpa using hj)
  have hderiv {x : ℝ} (hx : 0 < x) :
      HasDerivAt h (deriv G x * (-1 / q) * G x ^ (-1 / q - 1)) x := by
    exact (hGdiff x hx).hasDerivAt.rpow_const (Or.inl (ne_of_gt (hGpos x hx)))
  have hexp : -1 / q - 1 = -((q + 1) / q) := by field_simp; ring
  have hineq : ∀ x > 0, h x - 1 ≤ x * deriv h x := by
    intro x hx
    rw [(hderiv hx).deriv, hexp]
    have hp : G x * G x ^ (-((q + 1) / q)) = h x := by
      change G x * G x ^ (-((q + 1) / q)) = G x ^ (-1 / q)
      conv_lhs => lhs; rw [← Real.rpow_one (G x)]
      rw [← Real.rpow_add (hGpos x hx)]
      congr 1
      field_simp
      ring
    have heq : x * (deriv G x * (-1 / q) * G x ^ (-((q + 1) / q))) =
        h x - J x * G x ^ (-((q + 1) / q)) := by
      calc
        _ = (x * deriv G x) * (-1 / q) * G x ^ (-((q + 1) / q)) := by ring
        _ = q * (J x - G x) * (-1 / q) * G x ^ (-((q + 1) / q)) := by rw [hODE x hx]
        _ = G x * G x ^ (-((q + 1) / q)) -
            J x * G x ^ (-((q + 1) / q)) := by field_simp; ring
        _ = _ := by rw [hp]
    rw [heq]
    linarith [hGI hx]
  have hd0 : HasDerivWithinAt h D (Ici 0) 0 := by
    have ht := hGderiv0.rpow_const (p := -1 / q) (Or.inl (by rw [hG0]; norm_num))
    convert ht using 1
    simp [hG0]
    field_simp
  have hh0 : h 0 = 1 := by simp [h, hG0]
  have hlim : Tendsto (fun x => (h x - 1) / x) (𝓝[>] (0 : ℝ)) (𝓝 D) := by
    have ht := hasDerivWithinAt_iff_tendsto_slope.mp hd0
    have hs : Ici (0 : ℝ) \ {0} = Ioi 0 := by simp
    change Tendsto (fun x => slope h 0 x) _ _ at ht
    simpa only [hs, slope_def_field, hh0, sub_zero] using ht
  have hbound : 1 + D * a ≤ h a :=
    secant_lower_bound (fun x hx => (hderiv hx).differentiableAt) hineq hlim ha
  have hj : J a ≤ G a ^ ((q + 1) / q) := by
    have ht := Real.rpow_le_rpow (Real.rpow_nonneg (hJnonneg a ha) _)
      (hJle a ha) (le_of_lt (div_pos hqp hq))
    rw [← Real.rpow_mul (hJnonneg a ha)] at ht
    have he : q / (q + 1) * ((q + 1) / q) = 1 := by field_simp
    simpa [he] using ht
  have hepower : G a ^ ((q + 1) / q) = h a ^ (-(q + 1)) := by
    dsimp [h]
    rw [← Real.rpow_mul (le_of_lt (hGpos a ha))]
    congr 1
    ring
  rw [hepower] at hj
  exact hj.trans (Real.rpow_le_rpow_of_nonpos (by positivity) hbound (by linarith))

namespace ChordTransform

open MeasureTheory

noncomputable def kernel (n b a : ℝ) : ℝ := (1 + a*b) ^ (-n)

lemma kernel_pos {n b a : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ a) : 0 < kernel n b a :=
  Real.rpow_pos_of_pos (by positivity) _

lemma kernel_le_one {n b a : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b) (ha : 0 ≤ a) :
    kernel n b a ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith) (by linarith)

lemma kernel_hasDerivAt {n b a : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ a) :
    HasDerivAt (kernel n b) (-n*b*(1+a*b)^(-n-1)) a := by
  have h := (((hasDerivAt_id a).mul_const b).const_add 1).rpow_const
    (p := -n) (Or.inl (by positivity : 1+a*b ≠ 0))
  convert h using 1
  · rfl
  · dsimp
    ring

lemma kernel_deriv_bound {n b a : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b) (ha : 0 ≤ a) :
    ‖-n*b*(1+a*b)^(-n-1)‖ ≤ n*b := by
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith : 1 ≤ 1+a*b)
    (show -n-1 ≤ 0 by linarith)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg hn,
    abs_of_nonneg hb, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (mul_nonneg hn hb)

lemma kernel_lipschitzOn {n b : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b) :
    LipschitzOnWith ⟨n*b, mul_nonneg hn hb⟩ (kernel n b) (Ici 0) := by
  apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun a ha => (kernel_hasDerivAt hb ha).hasDerivWithinAt)
  intro a ha
  exact kernel_deriv_bound hn hb ha

lemma kernel_slope_bound {n b a : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b) (ha : 0 < a) :
    ‖(kernel n b a - 1) / a‖ ≤ n*b := by
  have h := (kernel_lipschitzOn hn hb).dist_le_mul a ha.le 0 (by simp)
  simp only [kernel, zero_mul, add_zero, Real.one_rpow, Real.dist_eq,
    sub_zero, abs_of_pos ha] at h
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha]
  exact (div_le_iff₀ ha).mpr h

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

noncomputable def transform (n : ℝ) (b : α → ℝ) (a : ℝ) : ℝ :=
  ∫ x, kernel n (b x) a ∂μ

omit [IsProbabilityMeasure μ] in
lemma kernel_aestronglyMeasurable {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    (n a : ℝ) : AEStronglyMeasurable (fun x => kernel n (b x) a) μ :=
  ((hb.aemeasurable.const_mul a).const_add 1 |>.pow_const (-n)).aestronglyMeasurable

lemma kernel_integrable {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x) {n a : ℝ} (hn : 0 ≤ n) (ha : 0 ≤ a) :
    Integrable (fun x => kernel n (b x) a) μ := by
  apply (integrable_const (1 : ℝ)).mono' (kernel_aestronglyMeasurable μ hb n a)
  filter_upwards [hb0] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (kernel_pos hx ha)]
  exact kernel_le_one hn hx ha

lemma transform_zero (n : ℝ) (b : α → ℝ) : transform μ n b 0 = 1 := by
  simp only [transform, kernel, zero_mul, add_zero, Real.one_rpow, integral_const,
    Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]

omit [IsProbabilityMeasure μ] in
lemma transform_nonneg {b : α → ℝ} (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x) {n a : ℝ}
    (ha : 0 ≤ a) : 0 ≤ transform μ n b a := by
  exact integral_nonneg_of_ae (hb0.mono fun _ hx => (kernel_pos hx ha).le)

lemma transform_pos {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x) {n a : ℝ} (hn : 0 ≤ n) (ha : 0 ≤ a) :
    0 < transform μ n b a := by
  apply (integral_pos_iff_support_of_nonneg_ae
    (hb0.mono fun _ hx => (kernel_pos hx ha).le) (kernel_integrable μ hb hb0 hn ha)).mpr
  have heq : Function.support (fun x => kernel n (b x) a) =ᵐ[μ] univ := by
    filter_upwards [hb0] with x hx
    apply propext
    change (kernel n (b x) a ≠ 0) ↔ True
    exact iff_true_intro (kernel_pos hx ha).ne'
  rw [measure_congr heq, measure_univ]
  norm_num

lemma transform_lipschitzOn {b : α → ℝ} (hb : Integrable b μ)
    (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x) {n : ℝ} (hn : 0 ≤ n) :
    LipschitzOnWith ⟨n * ∫ x, b x ∂μ, mul_nonneg hn (integral_nonneg_of_ae hb0)⟩
      (transform μ n b) (Ici 0) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha c hc
  have hia := kernel_integrable μ hb.aestronglyMeasurable hb0 hn ha
  have hic := kernel_integrable μ hb.aestronglyMeasurable hb0 hn hc
  change |(∫ x, kernel n (b x) a ∂μ) - ∫ x, kernel n (b x) c ∂μ| ≤ _
  rw [← integral_sub hia hic, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x, ‖kernel n (b x) a - kernel n (b x) c‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, n * b x * dist a c ∂μ := by
      apply integral_mono_ae (hia.sub hic).norm ((hb.const_mul n).mul_const _)
      filter_upwards [hb0] with x hx
      exact (kernel_lipschitzOn hn hx).dist_le_mul a ha c hc
    _ = (n * ∫ x, b x ∂μ) * dist a c := by
      rw [integral_mul_const, integral_const_mul]

lemma transform_hasDerivAt {b : α → ℝ} (hb : Integrable b μ)
    (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x) {n a : ℝ} (hn : 0 ≤ n) (ha : 0 < a) :
    HasDerivAt (transform μ n b)
      (∫ x, -n*b x*(1+a*b x)^(-n-1) ∂μ) a := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioi 0) (Ioi_mem_nhds ha)
    (Eventually.of_forall fun t => kernel_aestronglyMeasurable μ hb.aestronglyMeasurable n t)
    (kernel_integrable μ hb.aestronglyMeasurable hb0 hn ha.le)
    (F' := fun t x => -n*b x*(1+t*b x)^(-n-1))
    (bound := fun x => n*b x) ?_ ?_ (hb.const_mul n) ?_).2
  · exact ((hb.aestronglyMeasurable.const_mul (-n)).aemeasurable.mul
      (((hb.aemeasurable.const_mul a).const_add 1).pow_const (-n-1))).aestronglyMeasurable
  · filter_upwards [hb0] with x hx
    intro t ht
    exact kernel_deriv_bound hn hx ht.le
  · filter_upwards [hb0] with x hx
    intro t ht
    exact kernel_hasDerivAt hx ht.le

lemma transform_hasDerivWithinAt_zero {b : α → ℝ} (hb : Integrable b μ)
    (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x) {n : ℝ} (hn : 0 ≤ n) :
    HasDerivWithinAt (transform μ n b) (-n * ∫ x, b x ∂μ) (Ici 0) 0 := by
  have hlim : Tendsto (fun t => ∫ x, (kernel n (b x) t - 1) / t ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, -n*b x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => n*b x)
    · exact Eventually.of_forall fun t =>
        (((kernel_aestronglyMeasurable μ hb.aestronglyMeasurable n t).aemeasurable.sub_const 1).div_const t).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact hb0.mono fun x hx => kernel_slope_bound hn hx ht
    · exact hb.const_mul n
    · filter_upwards [hb0] with x hx
      have ht := hasDerivWithinAt_iff_tendsto_slope.mp
        ((kernel_hasDerivAt (n := n) hx (le_refl (0 : ℝ))).hasDerivWithinAt (s := Ici 0))
      have hs : Ici (0 : ℝ) \ {0} = Ioi 0 := by simp
      change Tendsto (fun t => slope (kernel n (b x)) 0 t) _ _ at ht
      simpa only [hs, slope_def_field, kernel, zero_mul, add_zero, Real.one_rpow,
        mul_one, sub_zero] using ht
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hs : Ici (0 : ℝ) \ {0} = Ioi 0 := by simp
  rw [hs]
  have hfg : (fun t => ∫ x, (kernel n (b x) t - 1) / t ∂μ) =ᶠ[𝓝[>] (0 : ℝ)]
      slope (transform μ n b) 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [integral_div, integral_sub (kernel_integrable μ hb.aestronglyMeasurable hb0 hn ht.le)
      (integrable_const 1), integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    rw [slope_def_field, transform_zero, sub_zero]
    rfl
  simpa only [integral_const_mul] using (hlim.congr' hfg)

end ChordTransform

end CAT0Fillings

namespace CAT0Fillings.ChordAverage

noncomputable def average (q : ℝ) (J : ℝ → ℝ) (a : ℝ) : ℝ :=
  q * ∫ u in (0 : ℝ)..1, J (a*u) * u^(q-1)

lemma integrable_weight {q : ℝ} (hq : 0 < q) (a : ℝ) :
    IntervalIntegrable (fun u : ℝ => u^(q-1)) volume 0 a :=
  intervalIntegral.intervalIntegrable_rpow' (by linarith)

lemma weight_integral {q : ℝ} (hq : 0 < q) :
    ∫ u in (0 : ℝ)..1, u^(q-1) = 1/q := by
  rw [integral_rpow (Or.inl (by linarith))]
  simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hq.ne', sub_zero]

lemma integrable_weighted {q : ℝ} (hq : 0 < q) {J : ℝ → ℝ}
    (hJ : ContinuousOn J (Ici 0)) {a : ℝ} (ha : 0 ≤ a) :
    IntervalIntegrable (fun t => J t * t^(q-1)) volume 0 a := by
  apply (integrable_weight hq a).continuousOn_mul
  rw [uIcc_of_le ha]
  exact hJ.mono fun _ hx => hx.1

lemma integrable_average {q : ℝ} (hq : 0 < q) {J : ℝ → ℝ}
    (hJ : ContinuousOn J (Ici 0)) {a : ℝ} (ha : 0 ≤ a) :
    IntervalIntegrable (fun u => J (a*u) * u^(q-1)) volume 0 1 := by
  apply (integrable_weight hq 1).continuousOn_mul
  apply hJ.comp (continuous_const.mul continuous_id).continuousOn
  intro u hu
  rw [uIcc_of_le zero_le_one] at hu
  exact mul_nonneg ha hu.1

lemma average_zero {q : ℝ} (hq : 0 < q) (J : ℝ → ℝ) :
    average q J 0 = J 0 := by
  simp only [average, zero_mul, intervalIntegral.integral_const_mul, weight_integral hq]
  field_simp

lemma average_rescale {q a : ℝ} (ha : 0 < a) (J : ℝ → ℝ) :
    average q J a = q * a^(-q) * ∫ t in (0 : ℝ)..a, J t * t^(q-1) := by
  have hc := intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (fun t => J t * t^(q-1)) ha.ne'
  have he : (∫ u in (0 : ℝ)..1, J (a*u) * (a*u)^(q-1)) =
      a^(q-1) * ∫ u in (0 : ℝ)..1, J (a*u) * u^(q-1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    dsimp only
    rw [Real.mul_rpow ha.le hu.1]
    ring
  rw [he, mul_zero, mul_one, smul_eq_mul] at hc
  have ha0 : a^(q-1) ≠ 0 := (Real.rpow_pos_of_pos ha _).ne'
  have hp : a^(-q) = a⁻¹ / a^(q-1) := by
    rw [Real.rpow_sub ha, Real.rpow_one, Real.rpow_neg ha.le]
    field_simp
  rw [average, hp]
  have hc' : (∫ u in (0 : ℝ)..1, J (a*u) * u^(q-1)) =
      (a⁻¹ * ∫ t in (0 : ℝ)..a, J t * t^(q-1)) / a^(q-1) := by
    apply (eq_div_iff ha0).mpr
    rwa [mul_comm]
  rw [hc']
  ring

lemma weighted_continuousOn {J : ℝ → ℝ} (hJ : ContinuousOn J (Ici 0)) (q : ℝ) :
    ContinuousOn (fun t => J t * t^(q-1)) (Ioi 0) :=
  (hJ.mono Ioi_subset_Ici_self).mul
    (continuousOn_id.rpow_const fun _ ht => Or.inl ht.ne')

lemma average_hasDerivAt {q : ℝ} (hq : 0 < q) {J : ℝ → ℝ}
    (hJ : ContinuousOn J (Ici 0)) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (average q J) (q/a * (J a - average q J a)) a := by
  let F : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, J u * u^(q-1)
  have hc := weighted_continuousOn hJ q
  have hF : HasDerivAt F (J a * a^(q-1)) a :=
    intervalIntegral.integral_hasDerivAt_right (integrable_weighted hq hJ ha.le)
      (hc.stronglyMeasurableAtFilter isOpen_Ioi a ha)
      (hc.continuousAt (Ioi_mem_nhds ha))
  have hd := (((hasDerivAt_id a).rpow_const (p := -q) (Or.inl ha.ne')).const_mul q).mul hF
  have he : average q J =ᶠ[𝓝 a] (fun t => q * t^(-q) * F t) := by
    filter_upwards [Ioi_mem_nhds ha] with t ht
    exact average_rescale ht J
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  dsimp only [id_eq]
  rw [average_rescale ha J]
  change q * (1 * -q * a^(-q-1)) * F a + q * a^(-q) * (J a * a^(q-1)) = _
  have hp : a^(-q-1) = a^(-q)/a := by rw [Real.rpow_sub ha, Real.rpow_one]
  have hp' : a^(-q) * a^(q-1) = a⁻¹ := by
    rw [← Real.rpow_add ha]
    ring_nf
    exact Real.rpow_neg_one a
  rw [hp]
  calc
    _ = -(q^2/a) * (a^(-q) * F a) + q * J a * (a^(-q) * a^(q-1)) := by ring
    _ = _ := by rw [hp']; simp only [F]; ring

lemma average_ode {q : ℝ} (hq : 0 < q) {J : ℝ → ℝ}
    (hJ : ContinuousOn J (Ici 0)) {a : ℝ} (ha : 0 < a) :
    a * deriv (average q J) a = q * (J a - average q J a) := by
  rw [(average_hasDerivAt hq hJ ha).deriv]
  field_simp

lemma average_pos {q : ℝ} (hq : 0 < q) {J : ℝ → ℝ}
    (hJ : ContinuousOn J (Ici 0)) (hpos : ∀ t ≥ 0, 0 < J t)
    {a : ℝ} (ha : 0 ≤ a) : 0 < average q J a := by
  apply mul_pos hq
  have hfi := integrable_average hq hJ ha
  have hpos' : ∀ u ∈ Ioc (0 : ℝ) 1, 0 < J (a*u)*u^(q-1) := by
    intro u hu
    exact mul_pos (hpos _ (mul_nonneg ha hu.1.le)) (Real.rpow_pos_of_pos hu.1 _)
  have hnonneg : 0 ≤ᵐ[volume.restrict (uIoc (0 : ℝ) 1)]
      (fun u => J (a*u)*u^(q-1)) := by
    rw [uIoc_of_le zero_le_one]
    exact (ae_restrict_mem measurableSet_Ioc).mono fun _ hu => (hpos' _ hu).le
  apply (intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hnonneg hfi).mpr
  refine ⟨zero_lt_one, ?_⟩
  have he : Function.support (fun u => J (a*u)*u^(q-1)) ∩ Ioc (0 : ℝ) 1 = Ioc 0 1 := by
    apply inter_eq_right.mpr
    intro u hu
    exact (hpos' u hu).ne'
  rw [he, Real.volume_Ioc]
  norm_num

lemma mul_weight {q u : ℝ} (hu : 0 < u) : u * u^(q-1) = u^q := by
  conv_lhs => lhs; rw [← Real.rpow_one u]
  rw [← Real.rpow_add hu]
  congr 1
  ring

lemma average_hasDerivWithinAt_zero {q : ℝ} (hq : 0 < q) {J : ℝ → ℝ}
    {K : ℝ≥0} (hLip : LipschitzOnWith K J (Ici 0)) {d : ℝ}
    (hd : HasDerivWithinAt J d (Ici 0) 0) :
    HasDerivWithinAt (average q J) (q/(q+1)*d) (Ici 0) 0 := by
  have hJ := hLip.continuousOn
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  have hi : ∀ t ≥ 0, Integrable (fun u => ((J (t*u)-J 0)/t)*u^(q-1)) μ := by
    intro t ht
    have h := ((integrable_average hq hJ ht).1.sub
      ((integrable_weight hq 1).1.const_mul (J 0))).div_const t
    convert h using 1
    funext u
    dsimp only [Pi.sub_apply]
    ring
  have hu : ∀ᵐ u ∂μ, u ∈ Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  have hlim : Tendsto (fun t => ∫ u, ((J (t*u)-J 0)/t)*u^(q-1) ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ u, d*u^q ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun u => (K : ℝ)*u^q)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hi t ht.le).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change (0 : ℝ) < t at ht
      filter_upwards [hu] with u hu
      have hb := hLip.dist_le_mul (t*u) (mul_pos ht hu.1).le 0 (by simp)
      simp only [Real.dist_eq, sub_zero, abs_of_pos (mul_pos ht hu.1)] at hb
      have hdiv : ‖(J (t*u)-J 0)/t‖ ≤ (K : ℝ)*u := by
        simp only [norm_div, Real.norm_eq_abs, abs_of_pos ht]
        apply (div_le_iff₀ ht).mpr
        nlinarith
      rw [norm_mul]
      rw [Real.norm_eq_abs (u ^ (q-1)), abs_of_nonneg (Real.rpow_nonneg hu.1.le _)]
      calc
        _ ≤ ((K : ℝ)*u)*u^(q-1) := mul_le_mul_of_nonneg_right hdiv (Real.rpow_nonneg hu.1.le _)
        _ = (K : ℝ)*u^q := by rw [mul_assoc, mul_weight hu.1]
    · exact ((intervalIntegral.intervalIntegrable_rpow' (show -1 < q by linarith)
        (a := 0) (b := 1)).1.const_mul (K : ℝ))
    · filter_upwards [hu] with u hu
      have hd' : HasDerivWithinAt (fun t => J (t*u)) (d*u) (Ici 0) 0 := by
        have hd0 : HasDerivWithinAt J d (Ici 0) (0*u) := by simpa only [zero_mul] using hd
        have hdu : HasDerivWithinAt (fun t : ℝ => t*u) u (Ici 0) 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).hasDerivWithinAt (s := Ici 0)
        exact hd0.comp 0 hdu (fun t ht => mul_nonneg ht hu.1.le)
      have ht := hasDerivWithinAt_iff_tendsto_slope.mp hd'
      have hs : Ici (0 : ℝ) \ {0} = Ioi 0 := by simp
      change Tendsto (fun t => slope (fun s => J (s*u)) 0 t) _ _ at ht
      simp only [hs, slope_def_field, zero_mul, sub_zero] at ht
      convert ht.mul_const (u^(q-1)) using 1
      rw [mul_assoc, mul_weight hu.1]
  have heq (t : ℝ) (ht : 0 < t) :
      q * (∫ u, ((J (t*u)-J 0)/t)*u^(q-1) ∂μ) =
        (average q J t - J 0)/t := by
    have hi1 : Integrable (fun u => J (t*u)*u^(q-1)) μ := (integrable_average hq hJ ht.le).1
    have hi0 : Integrable (fun u : ℝ => J 0*u^(q-1)) μ := (integrable_weight hq 1).1.const_mul _
    have hf : (fun u => ((J (t*u)-J 0)/t)*u^(q-1)) =
        (fun u => (J (t*u)*u^(q-1)-J 0*u^(q-1))/t) := by funext u; ring
    rw [hf, integral_div, integral_sub hi1 hi0, integral_const_mul]
    have hw : (∫ u : ℝ, u^(q-1) ∂μ) = 1/q := by
      rw [← intervalIntegral.integral_of_le zero_le_one]
      exact weight_integral hq
    rw [hw]
    have hj : (∫ u, J (t*u)*u^(q-1) ∂μ) =
        ∫ u in (0 : ℝ)..1, J (t*u)*u^(q-1) :=
      (intervalIntegral.integral_of_le zero_le_one).symm
    rw [hj, average]
    field_simp
  have hdlim := hlim.const_mul q
  have hlimval : q * (∫ u, d*u^q ∂μ) = q/(q+1)*d := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (show -1 < q by linarith))]
    rw [Real.one_rpow, Real.zero_rpow (show q+1 ≠ 0 by linarith), sub_zero]
    ring
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hs : Ici (0 : ℝ) \ {0} = Ioi 0 := by simp
  rw [hs]
  rw [hlimval] at hdlim
  apply hdlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [heq t ht, slope_def_field, average_zero hq, sub_zero]

end CAT0Fillings.ChordAverage

namespace CAT0Fillings.ChordTransform
open MeasureTheory

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

theorem distribution_bound {b : α → ℝ} (hb : Integrable b μ)
    (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x) {n : ℝ} (hn : 2 < n)
    (hvar : ∀ a > 0, (transform μ n b a)^((n-2)/n) ≤
      ChordAverage.average ((n-2)/2) (transform μ n b) a)
    {a : ℝ} (ha : 0 ≤ a) :
    transform μ n b a ≤ (1 + 2 * (∫ x, b x ∂μ) * a)^(-n/2) := by
  by_cases ha0 : a = 0
  · subst a
    simp [transform_zero]
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  let q := (n-2)/2
  have hq : 0 < q := by dsimp [q]; linarith
  have hn0 : 0 ≤ n := by linarith
  have hnne : n ≠ 0 := by linarith
  have hqp : q+1 ≠ 0 := by linarith
  have hnq : n = 2*(q+1) := by dsimp [q]; ring
  have hmean : 0 ≤ ∫ x, b x ∂μ := integral_nonneg_of_ae hb0
  have hlip := transform_lipschitzOn μ hb hb0 hn0
  have hc := hlip.continuousOn
  have hG0 : ChordAverage.average q (transform μ n b) 0 = 1 := by
    rw [ChordAverage.average_zero hq, transform_zero]
  have hd0 := ChordAverage.average_hasDerivWithinAt_zero hq hlip
    (transform_hasDerivWithinAt_zero μ hb hb0 hn0)
  have hd0' : HasDerivWithinAt (ChordAverage.average q (transform μ n b))
      (-q * (2 * ∫ x, b x ∂μ)) (Ici 0) 0 := by
    convert hd0 using 1
    rw [hnq]
    field_simp
  have hde : -(q+1) = -n/2 := by dsimp [q]; ring
  rw [← hde]
  apply chord_scalar_bound hq (mul_nonneg (by norm_num) hmean) hG0 hd0'
    (fun t ht => ChordAverage.average_pos hq hc (fun u hu => transform_pos μ
      hb.aestronglyMeasurable hb0 hn0 hu) ht.le)
    (fun t ht => transform_nonneg μ hb0 ht.le)
    (fun t ht => (ChordAverage.average_hasDerivAt hq hc ht).differentiableAt) ?_
    (fun t ht => ChordAverage.average_ode hq hc ht) ha'
  intro t ht
  have he : q/(q+1) = (n-2)/n := by
    apply (div_eq_div_iff hqp hnne).mpr
    dsimp [q]
    ring
  rw [he]
  exact hvar t ht

end CAT0Fillings.ChordTransform

open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.ChordIdentity

lemma rpow_shift_one {x r : ℝ} (hx : 0 < x) : x^(r+1) = x^r*x := by
  rw [Real.rpow_add hx, Real.rpow_one]

lemma rpow_shift_two {x r : ℝ} (hx : 0 < x) : x^(r+2) = x^r*x^2 := by
  rw [Real.rpow_add hx, Real.rpow_two]

lemma scalar_antiderivative {q b u : ℝ} (hb : 0 ≤ b) (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => u^q*(1+b*u)^(-2*q))
      (q*(u^(q-1)*(1+b*u)^(-2*q-2) - b^2*u^(q+1)*(1+b*u)^(-2*q-2))) u := by
  have hp : 0 < 1+b*u := by positivity
  have h1 := (hasDerivAt_id u).rpow_const (p := q) (Or.inl hu.ne')
  have h2 := (((hasDerivAt_id u).const_mul b).const_add 1).rpow_const
    (p := -2*q) (Or.inl hp.ne')
  apply (h1.mul h2).congr_deriv
  dsimp only [id_eq]
  have hu1 : u^q = u^(q-1)*u := by
    convert rpow_shift_one (r := q-1) hu using 1; congr 1; ring
  have hu2 : u^(q+1) = u^(q-1)*u^2 := by
    convert rpow_shift_two (r := q-1) hu using 1; congr 1; ring
  have hp1 : (1+b*u)^(-2*q-1) = (1+b*u)^(-2*q-2)*(1+b*u) := by
    convert rpow_shift_one (r := -2*q-2) hp using 1; congr 1; ring
  have hp2 : (1+b*u)^(-2*q) = (1+b*u)^(-2*q-2)*(1+b*u)^2 := by
    convert rpow_shift_two (r := -2*q-2) hp using 1; congr 1; ring
  rw [hu1, hu2, hp1, hp2]
  ring

lemma integral_weighted_kernel {r b s : ℝ} (hr : -1 < r) (hb : 0 ≤ b) :
    IntervalIntegrable (fun u : ℝ => u^r*(1+b*u)^s) volume 0 1 := by
  apply (intervalIntegral.intervalIntegrable_rpow' hr).mul_continuousOn
  apply (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).rpow_const
  intro u hu
  rw [uIcc_of_le zero_le_one] at hu
  have hu0 := hu.1
  exact Or.inl (ne_of_gt (by positivity : 0 < 1+b*u))

theorem scalar_identity {q b : ℝ} (hq : 0 < q) (hb : 0 ≤ b) :
    (1+b)^(-2*q) + q*b^2 * (∫ u in (0 : ℝ)..1, u^(q+1)*(1+b*u)^(-2*q-2)) =
      q * ∫ u in (0 : ℝ)..1, u^(q-1)*(1+b*u)^(-2*q-2) := by
  have hi1 := integral_weighted_kernel (r := q-1) (s := -2*q-2) (by linarith) hb
  have hi2 := integral_weighted_kernel (r := q+1) (s := -2*q-2) (by linarith) hb
  have hc : ContinuousOn (fun u : ℝ => u^q*(1+b*u)^(-2*q)) (Icc 0 1) := by
    apply ((continuousOn_id.rpow_const (fun _ _ => Or.inr hq.le))).mul
    apply (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).rpow_const
    intro u hu
    have hu0 := hu.1
    exact Or.inl (ne_of_gt (by positivity : 0 < 1+b*u))
  have hi : IntervalIntegrable (fun u : ℝ =>
      q*(u^(q-1)*(1+b*u)^(-2*q-2) - b^2*u^(q+1)*(1+b*u)^(-2*q-2))) volume 0 1 := by
    simpa only [mul_assoc] using (hi1.sub (hi2.const_mul (b^2))).const_mul q
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (a := (0 : ℝ)) (b := 1) zero_le_one hc
    (fun u hu => scalar_antiderivative hb hu.1) hi
  simp only [mul_one, Real.one_rpow, one_mul, mul_zero, add_zero,
    Real.zero_rpow hq.ne', sub_zero] at H
  rw [intervalIntegral.integral_const_mul] at H
  simp only [mul_assoc] at H
  rw [intervalIntegral.integral_sub hi1 (hi2.const_mul (b^2)),
    intervalIntegral.integral_const_mul] at H
  nlinarith [H]

end CAT0Fillings.ChordIdentity

namespace CAT0Fillings.ChordTransform
open MeasureTheory Set

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

lemma weighted_kernel_prod_integrable {b : α → ℝ}
    (hb : AEStronglyMeasurable b μ) (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x)
    {q n a : ℝ} (hq : 0 < q) (hn : 0 ≤ n) (ha : 0 ≤ a) :
    Integrable (fun z : α × ℝ => z.2^(q-1)*kernel n (b z.1) (a*z.2))
      (μ.prod (volume.restrict (Ioc 0 1))) := by
  let ρ : Measure ℝ := volume.restrict (Ioc 0 1)
  have hw : Integrable (fun u : ℝ => u^(q-1)) ρ :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < q-1)).1
  have hm : AEStronglyMeasurable
      (fun z : α × ℝ => z.2^(q-1)*kernel n (b z.1) (a*z.2)) (μ.prod ρ) := by
    have hs : AEMeasurable (fun z : α × ℝ => z.2) (μ.prod ρ) := measurable_snd.aemeasurable
    exact ((hs.pow_const (q-1)).mul
      ((((hs.const_mul a).mul hb.aemeasurable.comp_fst).const_add 1).pow_const (-n))).aestronglyMeasurable
  have hi : Integrable (fun z : α × ℝ => z.2^(q-1)) (μ.prod ρ) := by
    simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : α => (1 : ℝ)) μ).mul_prod hw
  apply hi.mono' hm
  have hc : ∀ᵐ z : α × ℝ ∂μ.prod ρ, 0 ≤ b z.1 :=
    Measure.quasiMeasurePreserving_fst.ae hb0
  have ht : ∀ᵐ z : α × ℝ ∂μ.prod ρ, z.2 ∈ Ioc (0 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hc, ht] with z hz ht
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.rpow_nonneg ht.1.le _) (kernel_pos hz (mul_nonneg ha ht.1.le)).le)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg ht.1.le _)
    (kernel_le_one hn hz (mul_nonneg ha ht.1.le))

theorem average_transform {b : α → ℝ}
    (hb : AEStronglyMeasurable b μ) (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x)
    {q n a : ℝ} (hq : 0 < q) (hn : 0 ≤ n) (ha : 0 ≤ a) :
    ChordAverage.average q (transform μ n b) a =
      ∫ x, q * (∫ u in (0 : ℝ)..1, u^(q-1)*kernel n (b x) (a*u)) ∂μ := by
  have hi := weighted_kernel_prod_integrable μ hb hb0 hq hn ha
  rw [ChordAverage.average, integral_const_mul]
  congr 1
  simp only [intervalIntegral.integral_of_le zero_le_one]
  have heq := integral_integral_swap (f := fun x u => u^(q-1)*kernel n (b x) (a*u)) hi
  rw [heq]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [integral_const_mul]
  simp only [transform, mul_comm]

theorem average_transform_scalar_identity {b : α → ℝ}
    (hb : AEStronglyMeasurable b μ) (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x)
    {q a : ℝ} (hq : 0 < q) (ha : 0 ≤ a) :
    ChordAverage.average q (transform μ (2*q+2) b) a =
      ∫ x, (1+a*b x)^(-2*q) + q*(a*b x)^2 *
        (∫ u in (0 : ℝ)..1, u^(q+1)*(1+a*b x*u)^(-2*q-2)) ∂μ := by
  rw [average_transform μ hb hb0 hq (by linarith) ha]
  apply integral_congr_ae
  filter_upwards [hb0] with x hx
  calc
    _ = q * ∫ u in (0 : ℝ)..1, u^(q-1)*(1+(a*b x)*u)^(-2*q-2) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp [kernel]
      congr 2 <;> ring
    _ = _ := (ChordIdentity.scalar_identity hq (mul_nonneg ha hx)).symm

end CAT0Fillings.ChordTransform
end

end OAI
