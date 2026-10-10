import OAI.Analysis.FourierLLogL.Fourier.Dirichlet
/-! # GoodBound from the dyadic lemma -/

open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology Real

namespace OAI

namespace FourierLLogL.Period
noncomputable section

private lemma center_sub : centerWin ⊆ window := by
  unfold centerWin window; grind

lemma sumReal_integral (ρ : ℝ → ℝ) (hρ : Measurable ρ) (h0 : ∀ x, 0 ≤ ρ x)
    (B : ℝ) (hb : ∀ x, ρ x ≤ B) (hp : Periodic ρ 1) (N : ℕ) (x : ℝ) :
    sumReal (fun y => (ρ y : ℂ)) N x =
      ∫ t in window, (ρ (x-t):ℂ) * centerWin.indicator (dirichlet N) t := by
  have hterm (n : ℤ) :
      (∫ y, (ρ y:ℂ) * phase (-n:ℤ) y ∂μ₁) * phase n x =
        ∫ t in centerWin, (ρ (x-t):ℂ) * phase n t := by
    let p (y : ℝ) := modρ ρ (-n:ℤ) y * phase n x
    have hpp : Periodic p 1 := by
      intro w
      simp only [p,modρ,hp w,phase_periodic (-n) w]
    have H (t : ℝ) : p (x-t) = (ρ (x-t) : ℂ) * phase n t := by
      dsimp only [p, modρ]; push_cast
      rw [mul_assoc, mul_comm (phase _ _), ← phase_sub,
        show x-(x-t)=t by ring]
    rw [← integral_mul_const]
    change (∫ y, p y ∂μ₁) = _
    simp_rw [← H]
    have HH := seg_translate_scale_rev p x (by norm_num : (-(1/2):ℝ)≤1/2)
      (by norm_num : (0:ℝ)<1)
    simp only [one_mul, inv_one, one_smul] at HH
    rw [show x-(-(1/2):ℝ) = (x-1/2)+1 by ring, seg_period_unit p hpp] at HH
    simpa only [centerWin, neg_div] using HH.symm
  have hxρ : Measurable fun t => (ρ (x-t):ℂ) :=
    Complex.continuous_ofReal.measurable.comp (hρ.comp (by fun_prop))
  have heq (t : ℝ) : (ρ (x-t):ℂ)*centerWin.indicator (dirichlet N) t =
      centerWin.indicator (fun t => (ρ (x-t):ℂ)*dirichlet N t) t := by
    by_cases ht : t ∈ centerWin <;> simp [ht]
  unfold sumReal
  simp_rw [hterm,heq]
  rw [setIntegral_indicator (show MeasurableSet centerWin from measurableSet_Ico), inter_eq_right.mpr center_sub]
  unfold dirichlet
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  intro n _
  refine seg_integrable _ (show Measurable (fun t => (ρ (x-t):ℂ)*phase n t)
    from hxρ.mul (phase_cont n).measurable) B _ _ fun t _ => ?_
  simp only [norm_mul, phase_unimod, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (h0 _), mul_one]
  exact hb _

private instance : IsFiniteMeasure (volume.restrict window) :=
  show IsFiniteMeasure (volume.restrict (Ico (-1:ℝ) 1)) from inferInstance

lemma kernel_compare_result (ρ : ℝ → ℝ) (hρ : Measurable ρ) (h0 : ∀ x, 0 ≤ ρ x)
    (B : ℝ) (hb : ∀ x, ρ x ≤ B) (hp : Periodic ρ 1)
    (hm : (∫ x, ρ x ∂μ₁) ≤ 1) (N J : ℕ)
    (hJ : 140 * ((N:ℝ)+1) * B * side J ≤ 1) (x : ℝ) :
    ENNReal.ofReal ‖sumReal (fun y => (ρ y:ℂ)) N x‖ ≤ 41 + 4 * maxConvK ρ J x := by
  let d := side J
  have hd := side_pos J
  have hd' := side_le J
  have hB : 0 ≤ B := le_trans (h0 0) (hb 0)
  let u : ℝ := N
  let w (t : ℝ) := ρ (x-t)
  let V (t : ℝ) : ℂ := kernel d t • modρ ρ u (x-t)
  have hwm : Measurable w := hρ.comp (by fun_prop)
  have hw (t : ℝ) : 0 ≤ w t := h0 _
  have hwB (t : ℝ) : w t ≤ B := hb _
  have hwi (a b) : IntervalIntegrable w volume a b :=
    interval_integrable w hwm B (fun t => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hw t)] using hwB t) a b
  have hw' : IntegrableOn w window :=
    Integrable.of_bound hwm.aestronglyMeasurable B (ae_of_all _ fun t => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hw t)] using hwB t)
  have hmass : (∫ t in window, w t) ≤ 2 := by
    have H := seg_translate_scale_rev ρ x (by norm_num : (-1:ℝ) ≤ 1)
      (by norm_num : (0:ℝ)<1)
    simp only [one_mul, inv_one, one_smul, sub_neg_eq_add] at H
    change (∫ t in Ico (-1:ℝ) 1, ρ (x-t)) ≤ 2
    have h := seg_period_int ρ hp (interval_integrable ρ hρ B (fun t => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (h0 t)] using hb t)) (x-1) 2
    rw [H, show x+1=x-1+(↑(2:ℕ) : ℝ) by norm_num; ring, h]
    simp; linarith
  have hVi : IntegrableOn V window := by
    have hVm : Measurable V := (kernel_measurable _).smul
      ((measurable_mod hρ u).comp (by fun_prop))
    apply Integrable.of_bound hVm.aestronglyMeasurable ((2/d)*B)
    apply ae_of_all
    intro t
    dsimp only [V]
    rw [norm_smul, norm_mod h0]
    exact mul_le_mul (kernel_small hd hd' _) (hb _) (h0 _) (div_nonneg (by norm_num) hd.le)
  let c := phase (-u) x
  let A : ℝ → ℂ := fun t => (w t:ℂ)* ↑(κfactor * kernel d t * Real.sin (ang u t))
  have hA (t) : A t = ↑((-κfactor)*(c * V t).im) := by
    have heq : c * V t = ↑(kernel d t)* (w t:ℂ) * phase u (-t) := by
      simp only [V,c,modρ,w,sub_eq_add_neg, phase_add, Complex.real_smul]
      have H : phase (-u) x * phase u x = 1 := by rw [← phase_freq_add]; simp [phase]
      linear_combination ↑(kernel d t) * (↑(ρ (x + -t)):ℂ) * phase u (-t) * H
    rw [heq, phase_trig]
    simp [A, ang, -Complex.ofReal_sin, -Complex.ofReal_cos]; ring
  have hiA : IntegrableOn A window := by

    have h : Integrable (fun t => c * V t) (volume.restrict window) := hVi.const_mul _
    rw [show A = _ from funext hA]
    exact Integrable.ofReal (h.im.const_mul _)
  have heA : (∫ t in window, A t) = ↑((-κfactor)*(c * convK (modρ ρ u) x J).im) := by
    simp_rw [hA]
    rw [integral_complex_ofReal, integral_const_mul]
    have h : Integrable (fun t => c * V t) (volume.restrict window) := hVi.const_mul _
    have hh := integral_im h
    change (∫ t in window, (c * V t).im) = (∫ t in window, c * V t).im at hh
    rw [hh, integral_const_mul]; rfl
  let T (t : ℝ) := (w t:ℂ) * centerWin.indicator (dirichlet N) t
  have hiT : IntegrableOn T window := by
    have h : Measurable T := (Complex.continuous_ofReal.measurable.comp hwm).mul
      ((dirichlet_cont _).measurable.indicator measurableSet_Ico)
    apply Integrable.of_bound h.aestronglyMeasurable (B*(2*N+1))
    apply ae_of_all
    intro t
    simp only [T, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw t)]
    apply mul_le_mul (hwB _) ?_ (norm_nonneg _) hB
    by_cases ht : t ∈ centerWin
    · simpa [ht] using dirichlet_bound N t
    · simp only [indicator_of_notMem ht, norm_zero]; positivity
  let M := (70:ℝ) * ((N:ℝ)+1)
  let S : Set ℝ := Ico (-d) d
  have hSm : MeasurableSet S := measurableSet_Ico
  have hSw : S ⊆ window := Ico_subset_Ico (neg_le_neg hd') hd'
  let W (t : ℝ) := S.indicator (fun _ => M*B) t
  have hiW : IntegrableOn W window := (integrable_const _).indicator hSm
  have heW : (∫ t in window, W t) ≤ 1 := by
    dsimp only [W]
    rw [setIntegral_indicator hSm, inter_eq_right.mpr hSw, setIntegral_const,
      Real.volume_real_Ico_of_le (by dsimp only [d]; linarith), smul_eq_mul]
    dsimp only [M,d]
    linarith
  have hei :
      ‖(∫ t in window, T t) - ∫ t in window, A t‖ ≤ 41 := by
    rw [← integral_sub hiT hiA]
    apply (norm_integral_le_integral_norm _).trans
    calc
      _ ≤ ∫ t in window, (20*w t + W t) := by
        apply integral_mono_ae (hiT.sub hiA).norm ((hw'.const_mul (20:ℝ)).add hiW)
        filter_upwards [ae_restrict_mem (show MeasurableSet window from measurableSet_Ico)]
          with t ht
        have hk : ‖T t - A t‖ = w t * ‖diffK d N t‖ := by
          dsimp only [T,A, diffK,u]
          rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw t)]
        change ‖T t - A t‖ ≤ 20*w t+W t
        have HH := diffK_major hd hd' ht N
        rw [hk]
        by_cases htd : |t| < d
        · rw [ite_eq_left (show |t| < side J from htd)] at HH
          have hs : t ∈ S := ⟨(abs_lt.mp htd).1.le,(abs_lt.mp htd).2⟩
          rw [show W t = M*B from indicator_of_mem hs _]
          change _ ≤ M at HH
          have : 0 ≤ M := by dsimp [M]; positivity
          have := mul_le_mul (hwB t) HH (norm_nonneg _) hB
          nlinarith [hw t]
        · rw [ite_eq_right (show ¬ |t| < side J from htd)] at HH
          have : 0 ≤ W t := by
            by_cases h : t ∈ S
            · rw [show W t = M*B from indicator_of_mem h _]
              dsimp [M]; positivity
            · rw [show W t = 0 from indicator_of_notMem h _]
          nlinarith [hw t]
      _ ≤ 41 := by rw [integral_add (hw'.const_mul (20:ℝ)) hiW, integral_const_mul]; linarith
  have hbound : ‖sumReal (fun y => (ρ y:ℂ)) N x‖ ≤ 41 + 4 * ‖convK (modρ ρ u) x J‖ := by
    rw [sumReal_integral ρ hρ h0 B hb hp]
    change ‖∫ t in window, T t‖ ≤ _
    have hh := le_trans (norm_sub_norm_le (∫ t in window, T t) (∫ t in window, A t)) hei
    rw [heA, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg] at hh
    have H1 := Complex.abs_im_le_norm (c * convK (modρ ρ u) x J)
    rw [norm_mul, show ‖c‖=1 from phase_unimod _ _, one_mul] at H1
    have := mul_le_mul κfactor_bound H1 (abs_nonneg _) (by norm_num)
    linarith
  apply (ENNReal.ofReal_le_ofReal hbound).trans
  rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_mul (by norm_num)]
  have Hle := le_iSup (fun n : ℤ => ENNReal.ofReal ‖convK (modρ ρ n) x J‖) (N:ℤ)
  simp only [Int.cast_natCast] at Hle
  norm_num

  gcongr
  rw [← ofReal_norm]; exact Hle


theorem AffineTreeBound.realGoodBound (h : AffineTreeBound) : RealGoodBound := by
  obtain ⟨C, hC, h⟩ := h
  let D := 100 + 64*C
  refine ⟨D, (show 0 ≤ 100+64*C by positivity), ?_⟩
  filter_upwards [h] with j hj
  intro ρ hρ hp h0 hm hb
  let B := Real.exp ((2:ℝ)^j)
  have hB : 0 < B := Real.exp_pos _
  obtain ⟨G,hG,hGs,hGc,hGd⟩ :=
    density_good_set ρ hρ hp h0 B hb hm (((j:ℝ)+1)^3) (by positivity)
  refine ⟨G,hG,hGc.trans (ENNReal.ofReal_le_ofReal ?_),?_⟩
  · have hn : (1:ℝ) ≤ (j:ℝ)+1 := by simp
    apply div_le_div₀
    all_goals first
      | dsimp [D]; positivity
      | positivity
      | dsimp [D]; linarith
      | gcongr; norm_num
  rw [μ₁, Measure.restrict_restrict hG, inter_eq_left.mpr hGs]
  let Y (N : ℕ) (x : ℝ) := ENNReal.ofReal ‖sumReal (fun y => (ρ y:ℂ)) N x‖
  let Ym (n : ℕ) (x : ℝ) := ⨆ N : ℕ, ⨆ (_ : N ≤ n), Y N x
  have hYm (n : ℕ) : Measurable (Ym n) := by
    refine Measurable.iSup fun N => Measurable.iSup fun _ => ?_
    refine Measurable.ennreal_ofReal (Measurable.norm (Continuous.measurable ?_))
    apply continuous_finsetSum
    intro k _
    exact continuous_const.mul (phase_cont _)
  have hYm_m : Monotone Ym := fun n m h x => iSup_le fun k => iSup_le fun hk =>
    le_iSup₂ (f:=fun N (_h : N ≤ m) => Y N x) k (le_trans hk h)
  have hmax (x : ℝ) : maxReal (fun y => (ρ y:ℂ)) x ≤ ⨆ n, Ym n x := by
    refine iSup_le fun n =>
      (le_iSup₂ (f := fun N (_h : N ≤ n) => Y N x) n le_rfl).trans (le_iSup (fun n => Ym n x) n)
  refine (lintegral_mono hmax).trans ?_
  rw [lintegral_iSup hYm hYm_m]
  refine iSup_le fun n => ?_
  have Hs : Tendsto side atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨J,hJ⟩ := ((show Tendsto (fun j => 140*((n:ℝ)+1)*B*side j) atTop (𝓝 0) by
    simpa only [mul_zero] using Hs.const_mul (140*((n:ℝ)+1)*B)).eventually
      (gt_mem_nhds (show (0:ℝ)<1 by norm_num))).exists
  change 140*((n:ℝ)+1)*B*side J < 1 at hJ
  have HL : (∫⁻ x in G, maxConvK ρ J x) ≤ 16 * ENNReal.ofReal (C*(2:ℝ)^j) :=
    convolution_cost hρ h0 B hb G hG hGs _ J
      (fun s hs a _ => hj ρ hρ hp h0 hm hb J G hG hGd a s hs.1 hs.2.le)
  have HE (x : ℝ) : Ym n x ≤ 41 + 4 * maxConvK ρ J x := by
    refine iSup_le fun k => iSup_le fun hk =>
      kernel_compare_result ρ hρ h0 B hb hp hm k J (le_trans ?_ hJ.le) x
    have := side_pos J
    gcongr
  refine (lintegral_mono HE).trans ?_
  rw [lintegral_add_left measurable_const,
    lintegral_const_mul _ (show Measurable (maxConvK ρ J) from measurable_maxConvK hρ J),
    setLIntegral_const]
  have hv : volume G ≤ 1 := (measure_mono hGs).trans (by simp [unitInt])
  calc
    _ ≤ 41 + 4*(16*ENNReal.ofReal (C*(2:ℝ)^j)) :=
      add_le_add (mul_le_of_le_one_right zero_le hv) (mul_le_mul_right HL _)
    _ = ENNReal.ofReal (41 + 4*(16*(C*(2:ℝ)^j))) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (show (0:ℝ)≤4 by norm_num),
        ENNReal.ofReal_mul (show (0:ℝ)≤16 by norm_num)]
      norm_num
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      dsimp [D]
      have H : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
      linarith)

end
end FourierLLogL.Period

end OAI
