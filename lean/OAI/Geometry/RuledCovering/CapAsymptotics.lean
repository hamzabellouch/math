import OAI.Geometry.RuledCovering.ConeVolume
import OAI.Geometry.RuledCovering.SingularOverlap

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma positivepart_increment {a h t : ℝ} (hh : 0 ≤ h) :
    0 ≤ max (a+h-t) 0-max (a-t) 0 ∧ max (a+h-t) 0-max (a-t) 0 ≤ h := by
  by_cases ht : t ≤ a
  · rw [max_eq_left (by linarith),max_eq_left (by linarith)]
    constructor <;> linarith
  · rw [show max (a-t) 0 = 0 from max_eq_right (by linarith), sub_zero]
    exact ⟨le_max_right _ _, max_le (by linarith) hh⟩

lemma positivepart_floor_increment {a d h t : ℝ} (hd : d ≤ a) (hh : 0 ≤ h) :
    max (a+h-max d t) 0-max (a-max d t) 0 = max (a+h-t) 0-max (a-t) 0 := by
  by_cases ht : t ≤ d
  · rw [max_eq_left ht,max_eq_left (by linarith),max_eq_left (by linarith),
      max_eq_left (by linarith),max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (le_of_not_ge ht)]

lemma rpow_five_halves_div_square {c : ℝ} (hc : 0 < c) :
    c^(5/2:ℝ)/c^2=c^(1/2:ℝ) := by
  rw [← Real.rpow_natCast,← Real.rpow_sub hc]
  norm_num

def capIncrementQuotient (p c b : ℝ) : ℝ :=
  (max ((1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ)-|b|) 0 -
    max ((1/2:ℝ)-|b|) 0)/c^2

lemma capIncrementQuotient_nonneg_bound {p c b : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (hc : 0 < c) :
    0 ≤ capIncrementQuotient p c b ∧
      capIncrementQuotient p c b ≤ ceilingPolynomial p b+c^(1/2:ℝ) := by
  have hd := ceiling_nonneg hp hp2 b
  have hi := positivepart_increment (a := (1/2:ℝ)) (t := |b|)
    (h := c^2*ceilingPolynomial p b+c^(5/2:ℝ)) (by positivity)
  have he : (c^2*ceilingPolynomial p b+c^(5/2:ℝ))/c^2 = ceilingPolynomial p b+c^(1/2:ℝ) := by
    rw [add_div,mul_div_cancel_left₀ _ (pow_ne_zero _ hc.ne'),rpow_five_halves_div_square hc]
  unfold capIncrementQuotient
  rw [← add_assoc] at hi
  exact ⟨div_nonneg hi.1 (sq_nonneg c),(div_le_div_of_nonneg_right hi.2 (sq_nonneg c)).trans_eq he⟩

lemma capIncrementQuotient_inside {p c b : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hc : 0 < c) (hb : |b| ≤ 1/2) :
    capIncrementQuotient p c b = ceilingPolynomial p b+c^(1/2:ℝ) := by
  have hd := ceiling_nonneg hp hp2 b
  have hn : 0 ≤ c^2*ceilingPolynomial p b+c^(5/2:ℝ) := by positivity
  unfold capIncrementQuotient
  rw [max_eq_left (by linarith),max_eq_left (by linarith)]
  have he : ((1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ)-|b|-(1/2-|b|)) =
      c^2*ceilingPolynomial p b+c^(5/2:ℝ) := by ring
  rw [he,add_div,mul_div_cancel_left₀ _ (pow_ne_zero _ hc.ne'),rpow_five_halves_div_square hc]

lemma ceilingPolynomial_continuous (p : ℝ) : Continuous (ceilingPolynomial p) := by
  unfold ceilingPolynomial
  fun_prop

lemma singular_ceiling_eventually (p : ℝ) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, ∀ b : ℝ, |b| ≤ 2 →
      (1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ) ≤ 2 := by
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (-2:ℝ)) (b := 2)).exists_bound_of_continuousOn
    (ceilingPolynomial_continuous p).continuousOn
  have ht : Tendsto (fun c : ℝ => c^2*C+c^(5/2:ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using ((h0.pow 2).mul_const C).add (right_rpow_tendsto_zero (q := (5/2:ℝ)) (by norm_num))
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<3/2))] with c hc b hb
  have h := (le_abs_self (ceilingPolynomial p b)).trans (by simpa only [Real.norm_eq_abs] using hC b (abs_le.mp hb))
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg c)
  linarith

lemma capIncrementQuotient_tendsto {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (b : ℝ) :
    Tendsto (fun c : ℝ => capIncrementQuotient p c b) (𝓝[>] 0)
      (𝓝 ((Icc (-(1/2:ℝ)) (1/2)).indicator (ceilingPolynomial p) b)) := by
  by_cases hb : |b| ≤ 1/2
  · rw [Set.indicator_of_mem (show b ∈ Icc (-(1/2:ℝ)) (1/2) from abs_le.mp hb)]
    have h : Tendsto (fun c : ℝ => ceilingPolynomial p b+c^(1/2:ℝ)) (𝓝[>] 0)
        (𝓝 (ceilingPolynomial p b)) := by
      simpa using (right_rpow_tendsto_zero (q := (1/2:ℝ)) (by norm_num)).const_add (ceilingPolynomial p b)
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact (capIncrementQuotient_inside hp hp2 hc hb).symm
  · rw [Set.indicator_of_notMem (by simpa only [mem_Icc,← abs_le] using hb)]
    have ht : Tendsto (fun c : ℝ => (1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ))
        (𝓝[>] 0) (𝓝 (1/2:ℝ)) := by
      have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.add ((h0.pow 2).mul_const (ceilingPolynomial p b))).add
        (right_rpow_tendsto_zero (q := (5/2:ℝ)) (by norm_num))
    apply tendsto_const_nhds.congr'
    filter_upwards [ht.eventually (gt_mem_nhds (lt_of_not_ge hb))] with c hc
    unfold capIncrementQuotient
    rw [max_eq_right (by linarith),max_eq_right (by linarith)]
    simp

lemma capIncrementQuotient_integral_tendsto {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    Tendsto (fun c : ℝ => ∫ b in Icc (-2:ℝ) 2, capIncrementQuotient p c b) (𝓝[>] 0)
      (𝓝 (∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b)) := by
  have hm : ∀ c : ℝ, Continuous (capIncrementQuotient p c) := by
    intro c
    unfold capIncrementQuotient
    exact (((continuous_const.add (continuous_const.mul (ceilingPolynomial_continuous p))).add continuous_const).sub continuous_abs).max continuous_const |>.sub
      ((continuous_const.sub continuous_abs).max continuous_const) |>.div_const _
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Icc (-2:ℝ) 2)) (fun b => ceilingPolynomial p b+1)
    (Filter.Eventually.of_forall (fun c => (hm c).aestronglyMeasurable))
    (show ∀ᶠ c : ℝ in 𝓝[>] 0, ∀ᵐ b ∂volume.restrict (Icc (-2:ℝ) 2),
      ‖capIncrementQuotient p c b‖ ≤ ceilingPolynomial p b+1 from by
      have he : ∀ᶠ c : ℝ in 𝓝[>] 0, c ≤ 1 :=
        (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds |>.mono (fun _ h => h.le)
      filter_upwards [self_mem_nhdsWithin,he] with c hc hc1
      exact Filter.Eventually.of_forall (fun b => by
        obtain ⟨h0,h1⟩ := capIncrementQuotient_nonneg_bound hp hp2 hc (b := b)
        rw [Real.norm_eq_abs,abs_of_nonneg h0]
        exact h1.trans (by linarith [Real.rpow_le_one (z := (1/2:ℝ)) hc.le hc1 (by norm_num)])))
    (((ceilingPolynomial_continuous p).add continuous_const).continuousOn.integrableOn_Icc)
    (Filter.Eventually.of_forall (capIncrementQuotient_tendsto hp hp2))
  have he : (∫ b in Icc (-2:ℝ) 2, (Icc (-(1/2:ℝ)) (1/2)).indicator (ceilingPolynomial p) b) =
      ∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b := by
    rw [integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
    congr 2
    apply Set.inter_eq_left.mpr
    intro b hb
    constructor <;> linarith [hb.1,hb.2]
  exact he ▸ h

lemma singularDomain_volume_difference {p gamma c : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hc : 0 < c) (hd : c^gamma ≤ (1/2:ℝ))
    (hcap : ∀ b : ℝ, |b| ≤ 2 → (1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ) ≤ 2) :
    (volume.real (singularDomain p gamma c)-(1/4-(c^gamma)^2))/c^2 =
      ∫ b in Icc (-2:ℝ) 2, capIncrementQuotient p c b := by
  have hv := coneBand_volume (d := c^gamma) (a := (1/2:ℝ)) (by positivity) hd
  norm_num at hv
  rw [← hv,singularDomain_volume_vertical p gamma c hcap,coneBand_volume_vertical (by norm_num)]
  have hI₁ : IntegrableOn (fun b : ℝ => max ((1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ)-max (c^gamma) |b|) 0)
      (Icc (-2:ℝ) 2) := by
    apply ContinuousOn.integrableOn_Icc
    apply Continuous.continuousOn
    exact (((continuous_const.add (continuous_const.mul (ceilingPolynomial_continuous p))).add continuous_const).sub
      (continuous_const.max continuous_abs)).max continuous_const
  have hI₂ : IntegrableOn (fun b : ℝ => max ((1/2:ℝ)-max (c^gamma) |b|) 0) (Icc (-2:ℝ) 2) := by
    apply ContinuousOn.integrableOn_Icc
    exact ((continuous_const.sub (continuous_const.max continuous_abs)).max continuous_const).continuousOn
  rw [← integral_sub hI₁ hI₂,← integral_div]
  apply setIntegral_congr_fun measurableSet_Icc
  intro b _
  unfold capIncrementQuotient
  apply congrArg (fun x : ℝ => x/c^2)
  have he := positivepart_floor_increment (a := (1/2:ℝ)) (d := c^gamma)
    (h := c^2*ceilingPolynomial p b+c^(5/2:ℝ)) (t := |b|) hd
    (by have := ceiling_nonneg hp hp2 b; positivity)
  simpa only [← add_assoc] using he

lemma singularDomain_volume_tendsto {p gamma : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (hg : 1 < gamma) :
    Tendsto (fun c : ℝ => (volume.real (singularDomain p gamma c)-1/4)/c^2) (𝓝[>] 0)
      (𝓝 (∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b)) := by
  have h := (capIncrementQuotient_integral_tendsto hp hp2).sub (singular_tip_small hg).tendsto_div_nhds_zero
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,singular_ceiling_eventually p,
    (right_rpow_tendsto_zero (lt_trans (by norm_num) hg)).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with c hc hcap hd
  rw [← singularDomain_volume_difference hp hp2 hc hd.le hcap]
  ring

end RuledApproximation

end

end OAI
