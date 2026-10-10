import OAI.Analysis.LpDimension.DyadicInterpolation

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset
open scoped BigOperators Topology Matrix ENNReal NNReal
universe u

namespace SubpolynomialLp

def tailPart (a x : ℝ) : ℝ := if a < |x| then x else 0

def cutPart (a x : ℝ) : ℝ := if |x| ≤ a then x else 0

def bandPart (a b x : ℝ) : ℝ := if a < |x| ∧ |x| ≤ b then x else 0

def dyadicRamp (ℓ : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range ℓ, bandPart ((2:ℝ)^k) (2^(k+ℓ)) x

@[fun_prop] lemma tailPart_measurable (a : ℝ) : Measurable (tailPart a) := by
  exact measurable_id.piecewise (measurableSet_lt measurable_const measurable_abs) measurable_const

@[fun_prop] lemma cutPart_measurable (a : ℝ) : Measurable (cutPart a) := by
  exact measurable_id.piecewise (measurableSet_le measurable_abs measurable_const) measurable_const

@[fun_prop] lemma bandPart_measurable (a b : ℝ) : Measurable (bandPart a b) := by
  exact measurable_id.piecewise ((measurableSet_lt measurable_const measurable_abs).inter
    (measurableSet_le measurable_abs measurable_const)) measurable_const

@[fun_prop] lemma dyadicRamp_measurable (ℓ : ℕ) : Measurable (dyadicRamp ℓ) := by
  exact Finset.measurable_sum _ (fun _ _ => bandPart_measurable _ _)

lemma tailPart_add_cutPart (a x : ℝ) : tailPart a x + cutPart a x = x := by
  unfold tailPart cutPart
  by_cases h : a < |x| <;> simp [h, le_of_not_gt, not_le.mpr]

lemma bandPart_eq_cutPart (a b x : ℝ) (hab : a ≤ b) :
    bandPart a b x = cutPart b x - cutPart a x := by
  unfold bandPart cutPart
  by_cases ha : a < |x| <;> by_cases hb : |x| ≤ b <;> simp [ha,hb,not_le.mpr,le_of_not_gt]
  exfalso; linarith


lemma abs_cutPart_le (a x : ℝ) (ha : 0 ≤ a) : |cutPart a x| ≤ a := by
  unfold cutPart
  split_ifs with h <;> simp_all

lemma bandPart_neg (a b x : ℝ) : bandPart a b (-x) = -bandPart a b x := by
  simp only [bandPart,abs_neg]
  split_ifs <;> simp

lemma dyadicRamp_neg (ℓ : ℕ) (x : ℝ) : dyadicRamp ℓ (-x) = -dyadicRamp ℓ x := by
  simp only [dyadicRamp,bandPart_neg,Finset.sum_neg_distrib]

lemma dyadicRamp_zero_small (ℓ : ℕ) (x : ℝ) (hx : |x| ≤ 1) : dyadicRamp ℓ x = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  have h : ¬ (2:ℝ)^k < |x| := not_lt.mpr (hx.trans (one_le_pow₀ (by norm_num)))
  simp [bandPart,h]

lemma abs_bandPart_le (a b x : ℝ) (hb : 0 ≤ b) : |bandPart a b x| ≤ b := by
  unfold bandPart
  split_ifs with h
  · exact h.2
  · simpa using hb

lemma abs_bandPart_le_tail (a b x : ℝ) : |bandPart a b x| ≤ |tailPart a x| := by
  unfold bandPart tailPart
  split_ifs <;> simp_all

lemma abs_dyadicRamp_le (ℓ : ℕ) (x : ℝ) : |dyadicRamp ℓ x| ≤ (2:ℝ)^(2*ℓ) := by
  calc
    |dyadicRamp ℓ x| ≤ ∑ k ∈ Finset.range ℓ, |bandPart ((2:ℝ)^k) (2^(k+ℓ)) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range ℓ, (2:ℝ)^(k+ℓ) :=
      Finset.sum_le_sum (fun k _ => abs_bandPart_le _ _ _ (by positivity))
    _ = (∑ k ∈ Finset.range ℓ, (2:ℝ)^k)*2^ℓ := by simp only [pow_add,Finset.sum_mul]
    _ ≤ (2:ℝ)^ℓ*2^ℓ := mul_le_mul_of_nonneg_right (two_sum_bound ℓ) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega


lemma dyadicRamp_plateau (m : ℕ) (x : ℝ)
    (hx : (2:ℝ)^(2*m) < x) (hx' : x ≤ (2:ℝ)^(3*m)) :
    (m:ℝ)*x ≤ dyadicRamp (2*m) x := by
  have hx0 : 0 ≤ x := (by positivity : (0:ℝ) < 2^(2*m)).le.trans hx.le
  have hb (k : ℕ) (hk : k ∈ Finset.Ico m (2*m)) :
      bandPart ((2:ℝ)^k) (2^(k+2*m)) x = x := by
    have hk' := Finset.mem_Ico.mp hk
    apply ite_eq_left
    rw [abs_of_nonneg hx0]
    exact ⟨lt_of_le_of_lt (pow_le_pow_right₀ (by norm_num) (by omega)) hx,
      hx'.trans (pow_le_pow_right₀ (by norm_num) (by omega))⟩
  calc
    (m:ℝ)*x = ∑ k ∈ Finset.Ico m (2*m), bandPart ((2:ℝ)^k) (2^(k+2*m)) x := by
      rw [Finset.sum_congr rfl hb]
      simp [show 2*m-m=m by omega]
    _ ≤ dyadicRamp (2*m) x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk; exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
      · intro k _ _; unfold bandPart; split_ifs <;> positivity

lemma pareto_integrable_moment (p q : ℝ) (hp : 0 < p) (hqp : q < p) :
    Integrable (fun r : ℝ => r^q) (pareto p) := by
  rw [pareto,powerIntensity,restrict_withDensity measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]
  apply (integrable_withDensity_iff_integrable_smul'
    (show Measurable (fun r : ℝ => ENNReal.ofReal (p*r^(-p-1))) by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
  have he : (fun r : ℝ => (ENNReal.ofReal (p*r^(-p-1))).toReal • r^q) =ᵐ[volume.restrict (Ioi 1)]
      fun r => p*r^(q-p-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := lt_trans zero_lt_one hr
    rw [ENNReal.toReal_ofReal (by positivity),smul_eq_mul,mul_assoc,← Real.rpow_add hr0]
    congr 2
    ring
  apply Integrable.congr _ he.symm
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : q-p-1 < -1) zero_lt_one).const_mul p

lemma pareto_tailPart_moment (p q a : ℝ) (hp : 0 < p) (hq : 0 < q) (hqp : q < p) (ha : 1 ≤ a) :
    (∫ r, |tailPart a r|^q ∂pareto p) = p/(p-q)*a^(q-p) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have he : (fun r => |tailPart a r|^q) =ᵐ[pareto p] (Ioi a).indicator (fun r : ℝ => r^q) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi (μ := powerIntensity p)] with r hr
    have hr0 : 0 < r := lt_trans zero_lt_one hr
    by_cases h : a < r
    · simp [tailPart,abs_of_pos hr0,h]
    · simp [tailPart,abs_of_pos hr0,h,Real.zero_rpow (by linarith : q ≠ 0)]
  rw [integral_congr_ae he,integral_indicator measurableSet_Ioi,pareto,
    Measure.restrict_restrict measurableSet_Ioi,Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi ha)]
  exact powerIntensity_large_moment p q a hp hqp ha0


lemma tailPart_abs_le (a x : ℝ) : |tailPart a x| ≤ |x| := by
  unfold tailPart
  split_ifs <;> simp

lemma tailPart_neg (a x : ℝ) : tailPart a (-x) = -tailPart a x := by
  simp only [tailPart,abs_neg]
  split_ifs <;> simp

lemma pareto_tail_sq_integrable (p a c : ℝ) (hp : 2 < p) (hc : |c| ≤ 1) :
    Integrable (fun r => (tailPart a (c*r))^2) (pareto p) := by
  have hi : Integrable (fun r : ℝ => r^2) (pareto p) := by
    simpa only [Real.rpow_two] using pareto_integrable_moment p 2 (by linarith) hp
  apply hi.mono' (show Measurable (fun r => (tailPart a (c*r))^2) by fun_prop).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi (μ := powerIntensity p)] with r hr
  have hr0 : 0 ≤ r := (lt_trans zero_lt_one hr).le
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hh : |tailPart a (c*r)| ≤ r := (tailPart_abs_le _ _).trans (by
    rw [abs_mul,abs_of_nonneg hr0]
    exact (mul_le_mul_of_nonneg_right hc hr0).trans_eq (one_mul _))
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr0).mpr hh

lemma pareto_tail_sq_moment (p a c : ℝ) (hp : 2 < p) (ha : 1 ≤ a) (hc : |c| ≤ 1) :
    (∫ r, (tailPart a (c*r))^2 ∂pareto p) = |c|^p*(p/(p-2)*a^(2-p)) := by
  have hf : ∀ x : ℝ, |x| ≤ 1 → |tailPart a x|^(2:ℝ) = 0 := by
    intro x hx
    simp [tailPart,not_lt.mpr (hx.trans ha)]
  have hs := pareto_even_scaling p c (by linarith) hc (fun x => |tailPart a x|^(2:ℝ))
    (fun x => by rw [tailPart_neg,abs_neg]) hf
  rw [pareto_tailPart_moment p 2 a (by linarith) (by norm_num) hp ha] at hs
  simpa only [Real.rpow_two,sq_abs] using hs

lemma dyadicRamp_moment_integrable (p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q) (ℓ : ℕ) :
    Integrable (fun r => |dyadicRamp ℓ r|^q) (pareto p) := by
  have := pareto_probability p hp
  apply Integrable.of_bound (by fun_prop (disch := positivity)) (((2:ℝ)^(2*ℓ))^q)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) (abs_dyadicRamp_le ℓ x) hq

lemma pareto_dyadicRamp_energy_lower (p : ℝ) (hp : 0 < p) (m : ℕ) (hm : 1 ≤ m) :
    p*Real.log 2*(m:ℝ)^(p+1) ≤ ∫ r, |dyadicRamp (2*m) r|^p ∂pareto p := by
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have ha : (1:ℝ) ≤ 2^(2*m) := one_le_pow₀ (by norm_num)
  have hab : (2:ℝ)^(2*m) ≤ 2^(3*m) := pow_le_pow_right₀ (by norm_num) (by omega)
  let s : Set ℝ := Ioc ((2:ℝ)^(2*m)) (2^(3*m))
  have hsi : IntegrableOn (fun r : ℝ => r^p) s (pareto p) := by
    have := pareto_probability p hp
    apply Integrable.of_bound (by fun_prop (disch := positivity)) (((2:ℝ)^(3*m))^p)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 ≤ r := ha.trans hr.1.le |>.trans' (by norm_num : (0:ℝ) ≤ 1)
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hr0 _)]
    exact Real.rpow_le_rpow hr0 hr.2 hp.le
  have him := dyadicRamp_moment_integrable p p hp hp.le (2*m)
  have hl : (∫ r in s, (m:ℝ)^p*r^p ∂pareto p) ≤
      ∫ r in s, |dyadicRamp (2*m) r|^p ∂pareto p := by
    apply integral_mono_ae (hsi.const_mul _) him.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 ≤ r := (by positivity : (0:ℝ) < 2^(2*m)).le.trans hr.1.le
    rw [← Real.mul_rpow hm0.le hr0]
    exact Real.rpow_le_rpow (by positivity)
      ((dyadicRamp_plateau m r hr.1 hr.2).trans (le_abs_self _)) hp.le
  have hrest : (∫ r in s, |dyadicRamp (2*m) r|^p ∂pareto p) ≤
      ∫ r, |dyadicRamp (2*m) r|^p ∂pareto p :=
    setIntegral_le_integral him (ae_of_all _ (fun r => Real.rpow_nonneg (abs_nonneg _) _))
  have he : (∫ r in s, (m:ℝ)^p*r^p ∂pareto p) = p*Real.log 2*(m:ℝ)^(p+1) := by
    rw [integral_const_mul,pareto,Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.mpr (show s ⊆ Ioi (1:ℝ) from fun r hr => ha.trans_lt hr.1)]
    rw [powerIntensity_critical_moment p _ _ hp (by positivity) hab,
      Real.log_div (by positivity) (by positivity),Real.log_pow,Real.log_pow,
      Real.rpow_add hm0,Real.rpow_one]
    push_cast
    ring
  exact he ▸ hl.trans hrest

lemma dyadic_variance_weight (p : ℝ) (k : ℕ) :
    (((2:ℝ)^((2-p)/2))^k)⁻¹*((2:ℝ)^k)^(2-p) = ((2:ℝ)^((2-p)/2))^k := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  ring

lemma pareto_dyadicRamp_variance (p : ℝ) (hp : 2 < p) (ℓ : ℕ) :
    (∫ r, (dyadicRamp ℓ r)^2 ∂pareto p) ≤
      (p/(p-2))/(1-(2:ℝ)^((2-p)/2))^2 := by
  let s : ℝ := (2:ℝ)^((2-p)/2)
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hs1 : s < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hi (k : ℕ) : Integrable (fun r => (tailPart ((2:ℝ)^k) r)^2) (pareto p) := by
    simpa only [one_mul] using pareto_tail_sq_integrable p ((2:ℝ)^k) 1 hp (by norm_num)
  have hJ : Integrable (fun r => (∑ k ∈ Finset.range ℓ, (s^k)⁻¹*(tailPart ((2:ℝ)^k) r)^2)/(1-s))
      (pareto p) := (integrable_finsetSum _ (fun k _ => (hi k).const_mul _)).div_const _
  have hM : Integrable (fun r => (dyadicRamp ℓ r)^2) (pareto p) := by
    simpa only [Real.rpow_two,sq_abs] using dyadicRamp_moment_integrable p 2 (by linarith) (by norm_num) ℓ
  have hpt (r : ℝ) : (dyadicRamp ℓ r)^2 ≤
      (∑ k ∈ Finset.range ℓ, (s^k)⁻¹*(tailPart ((2:ℝ)^k) r)^2)/(1-s) := by
    have ht : |dyadicRamp ℓ r| ≤ ∑ k ∈ Finset.range ℓ, |tailPart ((2:ℝ)^k) r| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun k _ => abs_bandPart_le_tail _ _ _))
    have hc := dyadic_cauchy s hs0 hs1 ℓ 0 (fun k => |tailPart ((2:ℝ)^k) r|)
    simp only [Nat.Ico_zero_eq_range,pow_zero,sq_abs,div_eq_mul_inv,one_mul] at hc
    have hh := (sq_le_sq₀ (abs_nonneg _) (Finset.sum_nonneg (fun k _ => abs_nonneg _))).mpr ht
    rw [sq_abs] at hh
    simpa only [div_eq_mul_inv] using hh.trans hc
  have hints (k : ℕ) : (∫ r, (tailPart ((2:ℝ)^k) r)^2 ∂pareto p) =
      p/(p-2)*((2:ℝ)^k)^(2-p) := by
    simpa only [one_mul,abs_one,Real.one_rpow] using
      pareto_tail_sq_moment p ((2:ℝ)^k) 1 hp (one_le_pow₀ (by norm_num)) (by norm_num)
  calc
    _ ≤ ∫ r, (∑ k ∈ Finset.range ℓ, (s^k)⁻¹*(tailPart ((2:ℝ)^k) r)^2)/(1-s) ∂pareto p :=
      integral_mono hM hJ hpt
    _ = (p/(p-2))*(∑ k ∈ Finset.range ℓ, s^k)/(1-s) := by
      rw [integral_div,integral_finsetSum _ (fun k _ => (hi k).const_mul _)]
      simp only [integral_const_mul,hints]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_left_comm,dyadic_variance_weight]
    _ ≤ (p/(p-2))*(1/(1-s))/(1-s) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Nat.Ico_zero_eq_range,pow_zero] using geometric_tail_bound s hs0.le hs1 0 ℓ
    _ = _ := by
      change (p/(p-2))*(1/(1-s))/(1-s) = (p/(p-2))/(1-s)^2
      field_simp

end SubpolynomialLp

end

end OAI
