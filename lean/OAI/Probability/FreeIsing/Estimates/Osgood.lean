import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Problem367

def osgoodTransform (K x : ℝ) : ℝ := Real.log (1 + Real.log (K / x))

lemma osgoodInner_pos {K x : ℝ} (hx : 0 < x) (hxK : x ≤ K) :
    0 < 1 + Real.log (K / x) := by
  have hratio : 1 ≤ K / x := (le_div_iff₀ hx).2 (by simpa using hxK)
  have hlog : 0 ≤ Real.log (K / x) := Real.log_nonneg hratio
  linarith

lemma hasDerivAt_osgoodTransform {K x : ℝ} (hx : 0 < x) (hxK : x ≤ K) :
    HasDerivAt (osgoodTransform K)
      (-1 / (x * (1 + Real.log (K / x)))) x := by
  have hK : 0 < K := hx.trans_le hxK
  have hratio : K / x ≠ 0 := ne_of_gt (div_pos hK hx)
  have hinner : 1 + Real.log (K / x) ≠ 0 := ne_of_gt (osgoodInner_pos hx hxK)
  have h := (((hasDerivAt_const x K).div (hasDerivAt_id x) (ne_of_gt hx)).log hratio).const_add 1
  convert! h.log hinner using 1
  dsimp
  field_simp
  ring

lemma continuousOn_criticalLogPrimitive {T : ℝ} (hT1 : T < 1) :
    ContinuousOn (fun t : ℝ => -(Real.log t)⁻¹) (Icc 0 T) := by
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    have hlim : Tendsto (fun t : ℝ => -(Real.log t)⁻¹) (𝓝[≠] 0) (𝓝 0) := by
      simpa using Real.tendsto_log_nhdsNE_zero.inv_tendsto_atBot.neg
    have hcont0 : ContinuousAt (fun t : ℝ => -(Real.log t)⁻¹) 0 := by
      rw [continuousAt_iff_punctured_nhds]
      simpa using hlim
    exact hcont0.continuousWithinAt
  · have ht1 : t ≠ 1 := by linarith [ht.2]
    have htm1 : t ≠ -1 := by linarith [ht.1]
    exact ((Real.hasDerivAt_inv_log ht0 ht1 htm1).neg).continuousAt.continuousWithinAt

lemma hasDerivAt_criticalLogPrimitive {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun t : ℝ => -(Real.log t)⁻¹)
      (1 / (t * (Real.log (1 / t)) ^ 2)) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have htm1 : t ≠ -1 := by linarith
  convert! (Real.hasDerivAt_inv_log ht0 ht1.ne htm1).neg using 1
  simp only [one_div, Real.log_inv, neg_sq, neg_div, neg_neg]
  field_simp

lemma criticalLogCoefficient_integrable {T : ℝ} (hT1 : T < 1) :
    IntegrableOn (fun t : ℝ => 1 / (t * (Real.log (1 / t)) ^ 2)) (Ioc 0 T) := by
  apply intervalIntegral.integrableOn_deriv_of_nonneg (continuousOn_criticalLogPrimitive hT1)
  · intro t ht
    exact hasDerivAt_criticalLogPrimitive ht.1 (ht.2.trans hT1)
  · intro t ht
    have : 0 < t := ht.1
    positivity

lemma criticalLogCoefficient_integral {T : ℝ} (hT : 0 ≤ T) (hT1 : T < 1) :
    (∫ t in (0 : ℝ)..T, 1 / (t * (Real.log (1 / t)) ^ 2)) =
      1 / Real.log (1 / T) := by
  have hint : IntervalIntegrable
      (fun t : ℝ => 1 / (t * (Real.log (1 / t)) ^ 2)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
      (criticalLogCoefficient_integrable hT1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (continuousOn_criticalLogPrimitive hT1)
    (fun t ht => hasDerivAt_criticalLogPrimitive ht.1 (ht.2.trans hT1)) hint
  simpa only [one_div, Real.log_inv, inv_neg, Real.log_zero, inv_zero, neg_zero, sub_zero] using h

lemma tendsto_osgoodTransform_nhdsGT_zero {K : ℝ} (hK : 0 < K) :
    Tendsto (osgoodTransform K) (𝓝[>] 0) atTop := by
  have hdiv : Tendsto (fun x : ℝ => K / x) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using
      (tendsto_inv_nhdsGT_zero : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) atTop).const_mul_atTop hK
  have hlog := Real.tendsto_log_atTop.comp hdiv
  have hinner : Tendsto (fun x : ℝ => 1 + Real.log (K / x)) (𝓝[>] 0) atTop := by
    simpa only [Function.comp_def, add_comm] using hlog.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  exact Real.tendsto_log_atTop.comp hinner

lemma criticalCoefficient_integrable {T : ℝ} (hT1 : T < 1) :
    IntegrableOn (fun t : ℝ => 1 + t ^ (-(3 : ℝ) / 4) +
      1 / (t * (Real.log (1 / t)) ^ 2)) (Ioc 0 T) := by
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (-(3 : ℝ) / 4)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 T) := by
    exact integrableOn_const (by simp)
  exact (hc.add hp.1).add (criticalLogCoefficient_integrable hT1)

lemma not_bounded_osgoodTransform_of_tendsto_zero {K C : ℝ} {v : ℕ → ℝ}
    (hK : 0 < K) (hv : Tendsto v atTop (𝓝 0)) (hpos : ∀ n, 0 < v n) :
    ¬ (∀ n, osgoodTransform K (v n) ≤ C) := by
  have hv' : Tendsto v atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hv, Eventually.of_forall hpos⟩
  have hh := (tendsto_osgoodTransform_nhdsGT_zero hK).comp hv'
  intro hbounded
  have hlarge := (tendsto_atTop.1 hh) (C + 1)
  obtain ⟨n, hn⟩ := hlarge.exists
  dsimp only [Function.comp_def] at hn
  linarith [hbounded n]

def osgoodModulus (K x : ℝ) : ℝ := x * (1 + Real.log (K / x))

lemma osgoodModulus_pos {K x : ℝ} (hx : 0 < x) (hxK : x ≤ K) :
    0 < osgoodModulus K x := mul_pos hx (osgoodInner_pos hx hxK)

lemma osgoodModulus_mono {K x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyK : y ≤ K) :
    osgoodModulus K x ≤ osgoodModulus K y := by
  have hy : 0 < y := hx.trans_le hxy
  have hK : 0 < K := hy.trans_le hyK
  have hlogKy : 0 ≤ Real.log (K / y) :=
    Real.log_nonneg ((le_div_iff₀ hy).2 (by simpa using hyK))
  have hlogyx := Real.log_le_sub_one_of_pos (div_pos hy hx)
  have hmul : x * Real.log (y / x) ≤ y - x := by
    have hh := mul_le_mul_of_nonneg_left hlogyx hx.le
    have heq : x * (y / x - 1) = y - x := by field_simp
    rwa [heq] at hh
  have hlog : Real.log (K / x) = Real.log (K / y) + Real.log (y / x) := by
    rw [Real.log_div hK.ne' hx.ne', Real.log_div hK.ne' hy.ne',
      Real.log_div hy.ne' hx.ne']
    ring
  unfold osgoodModulus
  rw [hlog]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hlogKy]

lemma osgoodModulus_mono_nonneg {K x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : 0 < y) (hyK : y ≤ K) : osgoodModulus K x ≤ osgoodModulus K y := by
  rcases eq_or_lt_of_le hx with h | h
  · subst x
    simpa [osgoodModulus] using (osgoodModulus_pos hy hyK).le
  · exact osgoodModulus_mono h hxy hyK

lemma osgood_regularized_deriv_bound {V : ℝ → ℝ} {K k t ε v' : ℝ}
    (hV : HasDerivAt V v' t) (hε : 0 < ε) (hv : 0 ≤ V t)
    (hK : V t + ε ≤ K) (hk : 0 ≤ k)
    (hbound : v' ≤ k * osgoodModulus K (V t)) :
    HasDerivAt (fun s => osgoodTransform K (V s + ε))
      (-v' / osgoodModulus K (V t + ε)) t ∧
      -k ≤ -v' / osgoodModulus K (V t + ε) := by
  have hpos : 0 < V t + ε := by linarith
  have hM : 0 < osgoodModulus K (V t + ε) := osgoodModulus_pos hpos hK
  have hm : osgoodModulus K (V t) ≤ osgoodModulus K (V t + ε) :=
    osgoodModulus_mono_nonneg hv (by linarith) hpos hK
  constructor
  · convert! (hasDerivAt_osgoodTransform hpos hK).comp t (hV.add_const ε) using 1
    dsimp [osgoodModulus]
    ring
  · have hh : v' ≤ k * osgoodModulus K (V t + ε) :=
      hbound.trans (mul_le_mul_of_nonneg_left hm hk)
    have hd := (div_le_iff₀ hM).2 hh
    simpa only [neg_div] using neg_le_neg hd

lemma osgoodTransform_antitone {K x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hyK : y ≤ K) : osgoodTransform K y ≤ osgoodTransform K x := by
  have hy : 0 < y := hx.trans_le hxy
  have hK : 0 < K := hy.trans_le hyK
  have hdiv : K / y ≤ K / x := div_le_div_of_nonneg_left hK.le hx hxy
  have hlog : Real.log (K / y) ≤ Real.log (K / x) :=
    Real.log_le_log (div_pos hK hy) hdiv
  exact Real.log_le_log (osgoodInner_pos hy hyK) (by linarith)

def criticalTimeCoefficient (cutoff C t : ℝ) : ℝ :=
  C * if t ≤ cutoff then
    1 + t ^ (-(3 : ℝ) / 4) + 1 / (t * (Real.log (1 / t)) ^ 2)
  else 1

lemma criticalTimeCoefficient_integrable (T C : ℝ) {cutoff : ℝ} (hc : cutoff < 1) :
    IntegrableOn (criticalTimeCoefficient cutoff C) (Ioc 0 T) := by
  have hearly : IntegrableOn
      (fun t : ℝ => 1 + t ^ (-(3 : ℝ) / 4) + 1 / (t * (Real.log (1 / t)) ^ 2))
      (Iic cutoff) (volume.restrict (Ioc 0 T)) := by
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Iic]
    exact (criticalCoefficient_integrable hc).mono_set (by
      intro t ht
      exact ⟨ht.2.1, ht.1⟩)
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 T) :=
    integrableOn_const (by simp)
  have hlate : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic cutoff)ᶜ
      (volume.restrict (Ioc 0 T)) := hconst.integrableOn
  have hpiece := Integrable.piecewise measurableSet_Iic hearly hlate
  change Integrable (fun t => criticalTimeCoefficient cutoff C t) (volume.restrict (Ioc 0 T))
  simpa only [criticalTimeCoefficient, Set.piecewise, Set.mem_Iic] using hpiece.const_mul C

lemma criticalTimeCoefficient_intervalIntegrable {T cutoff : ℝ} (C : ℝ)
    (hT : 0 ≤ T) (hc : cutoff < 1) :
    IntervalIntegrable (criticalTimeCoefficient cutoff C) volume 0 T := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
  exact criticalTimeCoefficient_integrable T C hc

lemma criticalTimeCoefficient_nonneg {cutoff C t : ℝ} (hC : 0 ≤ C) (ht : 0 < t) :
    0 ≤ criticalTimeCoefficient cutoff C t := by
  unfold criticalTimeCoefficient
  split_ifs <;> positivity

lemma criticalPowerCoefficient_integral (T : ℝ) :
    (∫ t in (0 : ℝ)..T, t ^ (-(3 : ℝ) / 4)) = 4 * T ^ ((1 : ℝ) / 4) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  norm_num
  ring

lemma criticalCoefficient_integral {T : ℝ} (hT : 0 ≤ T) (hT1 : T < 1) :
    (∫ t in (0 : ℝ)..T, 1 + t ^ (-(3 : ℝ) / 4) +
      1 / (t * (Real.log (1 / t)) ^ 2)) =
      T + 4 * T ^ ((1 : ℝ) / 4) + 1 / Real.log (1 / T) := by
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (-(3 : ℝ) / 4)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hl : IntervalIntegrable
      (fun t : ℝ => 1 / (t * (Real.log (1 / t)) ^ 2)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
      (criticalLogCoefficient_integrable hT1)
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add hp) hl,
    intervalIntegral.integral_add intervalIntegrable_const hp,
    criticalPowerCoefficient_integral, criticalLogCoefficient_integral hT hT1]
  simp

end Problem367

end

end OAI
