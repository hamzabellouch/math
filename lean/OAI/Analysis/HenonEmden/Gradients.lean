import OAI.Analysis.HenonEmden.CapMismatch

namespace OAI

universe uE uE2 uE3 uE4 uE5 uE6

section Gradients
open Set Filter Topology MeasureTheory MeasureTheory.Measure
open scoped RealInnerProductSpace ContDiff ENNReal Convolution Pointwise
noncomputable section
open HenonLaneEmden.RadialCalculus HenonLaneEmden.WeakPDE HenonLaneEmden.SphereCalculus

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def kernelDir (e x : E) : ℝ :=
  (2-(Module.finrank ℝ E:ℝ))*‖x‖^(-(Module.finrank ℝ E:ℝ))*⟪x,e⟫

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma hasFDerivAt_kernel {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖^(2-(Module.finrank ℝ E:ℝ)))
      (((2-(Module.finrank ℝ E:ℝ))*‖x‖^(-(Module.finrank ℝ E:ℝ))) • innerSL ℝ x) x := by
  have hr := norm_pos_iff.mpr hx
  have hd := RadialCalculus.hasFDerivAt_profile_norm hx
    (Real.hasDerivAt_rpow_const (p := 2-(Module.finrank ℝ E:ℝ)) (Or.inl hr.ne'))
  convert hd using 1
  congr 1
  rw [mul_div_assoc]
  congr 1
  calc
    _ = ‖x‖^(2-(Module.finrank ℝ E:ℝ)-1-1) := by congr 1; ring
    _ = _ := by rw [Real.rpow_sub hr,Real.rpow_one]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dir_kernel {e x : E} (hx : x ≠ 0) :
    dir (fun y : E => ‖y‖^(2-(Module.finrank ℝ E:ℝ))) e x = kernelDir e x := by
  rw [dir,(hasFDerivAt_kernel hx).fderiv]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma kernelDir_bound (e x : E) :
    |kernelDir e x| ≤ |2-(Module.finrank ℝ E:ℝ)| *‖e‖*‖x‖^(1-(Module.finrank ℝ E:ℝ)) := by
  by_cases hx : x = 0
  · simp only [hx,kernelDir,inner_zero_left,mul_zero,abs_zero,norm_zero]
    positivity
  have hr := norm_pos_iff.mpr hx
  unfold kernelDir
  rw [abs_mul,abs_mul,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have he : ‖x‖^(-(Module.finrank ℝ E:ℝ))*‖x‖ = ‖x‖^(1-(Module.finrank ℝ E:ℝ)) := by
    calc
      _ = ‖x‖^(-(Module.finrank ℝ E:ℝ)+1) := by rw [Real.rpow_add hr,Real.rpow_one]
      _ = _ := by congr 1; ring
  calc
    _ ≤ (|2-(Module.finrank ℝ E:ℝ)| *‖x‖^(-(Module.finrank ℝ E:ℝ)))*(‖x‖*‖e‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm x e) (by positivity)
    _ = |2-(Module.finrank ℝ E:ℝ)| *‖e‖*(‖x‖^(-(Module.finrank ℝ E:ℝ))*‖x‖) := by ring
    _ = _ := by rw [he]

lemma measurable_kernelDir (e : E) : Measurable (kernelDir e) :=
  (measurable_const.mul (measurable_norm.pow_const _)).mul (by fun_prop)

lemma locallyIntegrable_kernelDir (hn : 1 ≤ Module.finrank ℝ E) (e : E) :
    LocallyIntegrable (kernelDir e) := by
  apply locallyIntegrable_of_norm_le_rpow hn
    (α := (Module.finrank ℝ E:ℝ)-1) (C := |2-(Module.finrank ℝ E:ℝ)| *‖e‖) (by linarith)
    ?_ (measurable_kernelDir e).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  simpa only [Real.norm_eq_abs,neg_sub] using kernelDir_bound e x

lemma integral_kernel_dir_off_zero (hn : 1 ≤ Module.finrank ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (h0 : 0 ∉ tsupport φ) (e : E) :
    (∫ x, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*dir φ e x) = -(∫ x, kernelDir e x*φ x) := by
  have hK := locallyIntegrable_newtonKernel hn
  have hdφ : Continuous (dir φ e) := (contDiffOn_univ.mp
    (contDiffOn_dir (k := 1) hφ.contDiffOn isOpen_univ e)).continuous
  have hi := (locallyIntegrable_kernelDir hn e).integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have heq : (fun x => dir (fun y : E => ‖y‖^(2-(Module.finrank ℝ E:ℝ))) e x*φ x) =
      (fun x => kernelDir e x*φ x) := by
    ext x
    by_cases hx : x = 0
    · simp [hx,image_eq_zero_of_notMem_tsupport h0]
    · rw [dir_kernel hx]
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (v := e) (f := fun x : E => ‖x‖^(2-(Module.finrank ℝ E:ℝ))) (g := φ)
    (by change Integrable (fun x => dir (fun y : E => ‖y‖^(2-(Module.finrank ℝ E:ℝ))) e x*φ x); rw [heq]; exact hi)
    (hK.integrable_smul_right_of_hasCompactSupport hdφ (compactSupport_dir hc e))
    (hK.integrable_smul_right_of_hasCompactSupport hφ.continuous hc)
    (fun x hx => (hasFDerivAt_kernel (fun he => h0 (he ▸ hx))).differentiableAt)
    (fun x _ => hφ.differentiable (by norm_num) x)
  change (∫ x, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*dir φ e x) = -(∫ x, dir (fun y : E => ‖y‖^(2-(Module.finrank ℝ E:ℝ))) e x*φ x) at hh
  rwa [heq] at hh
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma kernel_cutoff_derivative_tendsto_zero (hn : 1 ≤ Module.finrank ℝ E) {φ : E → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (ξ : ContDiffBump (0:E)) (e : E) :
    Tendsto (fun R : ℝ => ∫ x : E, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*φ x*
      (R⁻¹*dir ξ e (R⁻¹ • x))) (𝓝[>] 0) (𝓝 0) := by
  have hdξ : Continuous (dir ξ e) := (contDiffOn_univ.mp
    (contDiffOn_dir (k := 1) (ξ.contDiff.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffOn isOpen_univ e)).continuous
  obtain ⟨M,hM⟩ := (compactSupport_dir ξ.hasCompactSupport e).exists_bound_of_continuous hdξ
  have hM0 : 0 ≤ M := (norm_nonneg (dir ξ e 0)).trans (hM 0)
  have hi : Integrable (fun x : E => ‖x‖^(1-(Module.finrank ℝ E:ℝ))*φ x) :=
    (locallyIntegrable_norm_power hn _ (by linarith)).integrable_smul_right_of_hasCompactSupport hφ hc
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝[>] (0:ℝ))
    (F := fun (R : ℝ) (x : E) => ‖x‖^(2-(Module.finrank ℝ E:ℝ))*φ x*(R⁻¹*dir ξ e (R⁻¹ • x)))
    (f := fun _ => (0:ℝ)) (fun x => (M*ξ.rOut)*‖‖x‖^(1-(Module.finrank ℝ E:ℝ))*φ x‖)
    (Eventually.of_forall fun R => by
      exact (((measurable_norm.pow_const _).mul hφ.measurable).mul
        (measurable_const.mul (hdξ.measurable.comp (measurable_const.smul measurable_id)))).aestronglyMeasurable)
    ?_ (hi.norm.const_mul (M*ξ.rOut)) ?_
  · simpa only [integral_zero] using hlim
  · filter_upwards [self_mem_nhdsWithin] with R hR
    filter_upwards [ae_iff.mpr (show volume {x : E | ¬ x ≠ 0} = 0 by simp)] with x hx
    by_cases hd : dir ξ e (R⁻¹ • x) = 0
    · simp only [hd,mul_zero,norm_zero]
      exact mul_nonneg (mul_nonneg hM0 ξ.rOut_pos.le) (norm_nonneg _)
    have hs := tsupport_dir_subset (ξ : E → ℝ) e (subset_tsupport _ hd)
    rw [ξ.tsupport_eq] at hs
    have hnorm : R⁻¹*‖x‖ ≤ ξ.rOut := by
      simpa only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (show 0 < R from hR))] using hs
    have hrx := norm_pos_iff.mpr hx
    have hb : R⁻¹ ≤ ξ.rOut/‖x‖ := (le_div_iff₀ hrx).mpr hnorm
    have hh : |R⁻¹*dir ξ e (R⁻¹ • x)| ≤ M*ξ.rOut/‖x‖ := by
      rw [abs_mul,abs_of_pos (inv_pos.mpr hR)]
      have hm' : |dir ξ e (R⁻¹ • x)| ≤ M := by simpa only [Real.norm_eq_abs] using hM (R⁻¹ • x)
      calc
        _ ≤ R⁻¹*M := mul_le_mul_of_nonneg_left hm' (inv_pos.mpr hR).le
        _ ≤ (ξ.rOut/‖x‖)*M := mul_le_mul_of_nonneg_right hb hM0
        _ = _ := by ring
    rw [norm_mul,Real.norm_eq_abs (R⁻¹*_),norm_mul,Real.norm_eq_abs (‖x‖^_),abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    apply (mul_le_mul_of_nonneg_left hh (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _))).trans_eq
    rw [norm_mul,Real.norm_eq_abs (‖x‖^_),abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    have he : ‖x‖^(2-(Module.finrank ℝ E:ℝ))/‖x‖ = ‖x‖^(1-(Module.finrank ℝ E:ℝ)) := by
      calc
        _ = ‖x‖^(2-(Module.finrank ℝ E:ℝ)-1) := by rw [Real.rpow_sub hrx (2-(Module.finrank ℝ E:ℝ)) 1,Real.rpow_one]
        _ = _ := by congr 1; ring
    calc
      _ = (M*ξ.rOut)*(‖x‖^(2-(Module.finrank ℝ E:ℝ))/‖x‖)*‖φ x‖ := by ring
      _ = _ := by rw [he]; ring
  · filter_upwards [ae_iff.mpr (show volume {x : E | ¬ x ≠ 0} = 0 by simp)] with x hx
    have he : 0 < ‖x‖/ξ.rOut := div_pos (norm_pos_iff.mpr hx) ξ.rOut_pos
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds he).filter_mono nhdsWithin_le_nhds] with R hR hlt
    have hs : R⁻¹ • x ∉ tsupport (ξ : E → ℝ) := by
      rw [ξ.tsupport_eq,Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
      apply not_le_of_gt
      rw [← div_eq_inv_mul]
      apply (lt_div_iff₀ hR).mpr
      simpa only [mul_comm] using (lt_div_iff₀ ξ.rOut_pos).mp hlt
    simp only [dir,fderiv_of_notMem_tsupport ℝ hs,_root_.zero_apply,mul_zero]
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma kernel_dir_cutoff_tendsto_zero (hn : 1 ≤ Module.finrank ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (ξ : ContDiffBump (0:E)) (e : E) :
    Tendsto (fun R : ℝ => ∫ x : E, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*
      dir (fun y => φ y*ξ (R⁻¹ • y)) e x) (𝓝[>] 0) (𝓝 0) := by
  have hK := locallyIntegrable_newtonKernel hn
  have hdφ : Continuous (dir φ e) := (contDiffOn_univ.mp
    (contDiffOn_dir (k := 1) hφ.contDiffOn isOpen_univ e)).continuous
  have hdξ : Continuous (dir ξ e) := (contDiffOn_univ.mp
    (contDiffOn_dir (k := 1) (ξ.contDiff.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffOn isOpen_univ e)).continuous
  have heq (R : ℝ) : (∫ x : E, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*dir (fun y => φ y*ξ (R⁻¹ • y)) e x) =
      (∫ x : E, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*(dir φ e x*ξ (R⁻¹ • x))) +
      (∫ x : E, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*φ x*(R⁻¹*dir ξ e (R⁻¹ • x))) := by
    have hξR : Differentiable ℝ (fun y : E => ξ (R⁻¹ • y)) :=
      ((ξ.contDiff : ContDiff ℝ 2 ξ).comp (contDiff_const.smul contDiff_id)).differentiable (by norm_num)
    simp_rw [dir_mul (hφ.differentiable (by norm_num) _) (hξR _) e,dir_dilation,mul_add,← mul_assoc]
    apply integral_add
    · simpa only [smul_eq_mul, Pi.mul_apply, Function.comp_apply, Pi.smul_apply, id_eq, mul_assoc] using
        hK.integrable_smul_right_of_hasCompactSupport
          (hdφ.mul (ξ.continuous.comp (continuous_id.const_smul R⁻¹))) (compactSupport_dir hc e).mul_right
    · simpa only [smul_eq_mul, Pi.mul_apply, Function.comp_apply, Pi.smul_apply, id_eq, mul_assoc] using
        hK.integrable_smul_right_of_hasCompactSupport
          (hφ.continuous.mul ((continuous_const : Continuous (fun _ : E => R⁻¹)).mul
            (hdξ.comp (continuous_id.const_smul R⁻¹)))) hc.mul_right
  simp_rw [heq]
  simpa only [add_zero] using (cutoff_source_integral_tendsto_zero hK hdφ (compactSupport_dir hc e) ξ).add
    (kernel_cutoff_derivative_tendsto_zero hn hφ.continuous hc ξ e)

lemma integral_kernel_dir (hn : 1 ≤ Module.finrank ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (e : E) :
    (∫ x, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*dir φ e x) = -(∫ x, kernelDir e x*φ x) := by
  let ξ : ContDiffBump (0:E) := ⟨1,2,by norm_num,by norm_num⟩
  have hK := locallyIntegrable_newtonKernel hn
  have hD := locallyIntegrable_kernelDir hn e
  have hdφ : Continuous (dir φ e) := (contDiffOn_univ.mp
    (contDiffOn_dir (k := 1) hφ.contDiffOn isOpen_univ e)).continuous
  have hiK := hK.integrable_smul_right_of_hasCompactSupport hdφ (compactSupport_dir hc e)
  have hiD := hD.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have hevent : ∀ᶠ R : ℝ in 𝓝[>] 0,
      (∫ x, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*dir φ e x) -
        (∫ x, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*dir (fun y => φ y*ξ (R⁻¹ • y)) e x) =
        -(∫ x, kernelDir e x*φ x)+(∫ x, kernelDir e x*(φ x*ξ (R⁻¹ • x))) := by
    filter_upwards [self_mem_nhdsWithin] with R hR
    obtain ⟨hψ,hψc,hψ0⟩ := cutoff_test_off_origin hφ hc ξ hR
    have hh := integral_kernel_dir_off_zero hn hψ hψc hψ0 e
    have hχ : ContDiff ℝ 2 (fun y : E => φ y*ξ (R⁻¹ • y)) :=
      hφ.mul (ξ.contDiff.comp (contDiff_const.smul contDiff_id))
    have hχc : HasCompactSupport (fun y : E => φ y*ξ (R⁻¹ • y)) := hc.mul_right
    have hdχ : Continuous (dir (fun y : E => φ y*ξ (R⁻¹ • y)) e) := (contDiffOn_univ.mp
      (contDiffOn_dir (k := 1) hχ.contDiffOn isOpen_univ e)).continuous
    have hiχK := hK.integrable_smul_right_of_hasCompactSupport hdχ (compactSupport_dir hχc e)
    have hiχD := hD.integrable_smul_right_of_hasCompactSupport hχ.continuous hχc
    simp only [smul_eq_mul] at hiK hiD hiχK hiχD
    have hid (x : E) : dir (fun y => φ y-φ y*ξ (R⁻¹ • y)) e x =
        dir φ e x-dir (fun y => φ y*ξ (R⁻¹ • y)) e x := by
      unfold dir
      exact congrArg (fun L : E →L[ℝ] ℝ => L e)
        ((hφ.differentiable (by norm_num) x).hasFDerivAt.sub
          (hχ.differentiable (by norm_num) x).hasFDerivAt).fderiv
    simp_rw [hid,mul_sub] at hh
    rw [integral_sub hiK hiχK,integral_sub hiD hiχD] at hh
    linarith
  have hlim₁ := (tendsto_const_nhds (x := ∫ x, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*dir φ e x)).sub
    (kernel_dir_cutoff_tendsto_zero hn hφ hc ξ e)
  have hlim₂ := (tendsto_const_nhds (x := -(∫ x, kernelDir e x*φ x))).add
    (cutoff_source_integral_tendsto_zero hD hφ.continuous hc ξ)
  simpa only [sub_zero,add_zero] using tendsto_nhds_unique hlim₁ (hlim₂.congr' (hevent.mono fun _ hh => hh.symm))
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE4} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma kernelDir_shift_bound (hn : 3 ≤ Module.finrank ℝ E) {r : ℝ} (hr : 0 < r)
    {x x₀ y : E} (hx : ‖x-x₀‖ < r/2) (hy : r ≤ ‖x₀-y‖) (e : E) :
    |kernelDir e (x-y)| ≤ (|2-(Module.finrank ℝ E:ℝ)| *‖e‖*(2/r)*(1/2:ℝ)^(2-(Module.finrank ℝ E:ℝ)))*
      ‖x₀-y‖^(2-(Module.finrank ℝ E:ℝ)) := by
  have ht := norm_sub_le (x₀-x) (y-x)
  simp only [sub_sub_sub_cancel_right,norm_sub_rev y x,norm_sub_rev x₀ x] at ht
  have hl : r/2 ≤ ‖x-y‖ := by linarith
  have hp : 0 < ‖x-y‖ := lt_of_lt_of_le (half_pos hr) hl
  have ha : 2-(Module.finrank ℝ E:ℝ) ≤ 0 := by
    have hh : (3:ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hn
    linarith
  have he : ‖x-y‖^(1-(Module.finrank ℝ E:ℝ)) = ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))/‖x-y‖ := by
    calc
      _ = ‖x-y‖^(2-(Module.finrank ℝ E:ℝ)-1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_sub hp,Real.rpow_one]
  have hh : ‖x-y‖^(1-(Module.finrank ℝ E:ℝ)) ≤
      (2/r)*((1/2:ℝ)^(2-(Module.finrank ℝ E:ℝ))*‖x₀-y‖^(2-(Module.finrank ℝ E:ℝ))) := by
    rw [he,div_eq_inv_mul]
    apply mul_le_mul
    · have h := one_div_le_one_div_of_le (half_pos hr) hl
      simpa only [one_div,inv_div] using h
    · exact rpow_kernel_shift_bound ha hr hx hy
    · positivity
    · positivity
  exact (kernelDir_bound e (x-y)).trans ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))

lemma hasLineDerivAt_far_rawPotential (hn : 3 ≤ Module.finrank ℝ E) {g : E → ℝ}
    (hg : Measurable g) (hgp : ∀ y, 0 ≤ g y) {x₀ : E} {r : ℝ} (hr : 0 < r)
    (hzero : ∀ y ∈ Metric.ball x₀ r, g y = 0)
    (hi : Integrable (fun y => ‖x₀-y‖^(2-(Module.finrank ℝ E:ℝ))*g y)) (e : E) :
    Integrable (fun y => kernelDir e (x₀-y)*g y) ∧
      HasLineDerivAt ℝ (rawPotential g) (∫ y, kernelDir e (x₀-y)*g y) x₀ e := by
  let C := |2-(Module.finrank ℝ E:ℝ)| *‖e‖*(2/r)*(1/2:ℝ)^(2-(Module.finrank ℝ E:ℝ))
  let s : Set ℝ := {t | ‖t • e‖ < r/2}
  have hs : s ∈ 𝓝 (0:ℝ) := by
    apply IsOpen.mem_nhds (isOpen_lt (continuous_id.smul continuous_const).norm continuous_const)
    simpa [s] using half_pos hr
  have hDmeas : Measurable (fun y : E => kernelDir e (x₀-y)*g y) :=
    ((measurable_kernelDir e).comp (measurable_const.sub measurable_id)).mul hg
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure E)) (F := fun (t : ℝ) (y : E) => ‖(x₀+t • e)-y‖^(2-(Module.finrank ℝ E:ℝ))*g y)
    (F' := fun (t : ℝ) (y : E) => kernelDir e ((x₀+t • e)-y)*g y)
    (bound := fun y => C*(‖x₀-y‖^(2-(Module.finrank ℝ E:ℝ))*g y)) hs
    (Eventually.of_forall fun t => (((measurable_const.sub measurable_id).norm.pow_const _).mul hg).aestronglyMeasurable)
    (by simpa using hi)
    (by simpa only [zero_smul, add_zero] using hDmeas.aestronglyMeasurable)
    ?_ (hi.const_mul C) ?_
  · simpa only [zero_smul,add_zero,HasLineDerivAt,rawPotential] using hh
  · apply Eventually.of_forall
    intro y t ht
    by_cases hy : y ∈ Metric.ball x₀ r
    · simp only [hzero y hy,mul_zero,norm_zero,le_refl]
    have hyr : r ≤ ‖x₀-y‖ := by
      have hy' : ¬ ‖y-x₀‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
      simpa only [norm_sub_rev] using le_of_not_gt hy'
    have htx : ‖(x₀+t • e)-x₀‖ < r/2 := by simpa only [s,Set.mem_ofPred_eq,add_sub_cancel_left] using ht
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (hgp y)]
    exact (mul_le_mul_of_nonneg_right (kernelDir_shift_bound hn hr htx hyr e) (hgp y)).trans_eq (mul_assoc _ _ _)
  · apply Eventually.of_forall
    intro y t ht
    by_cases hy : y ∈ Metric.ball x₀ r
    · simp only [hzero y hy,mul_zero]
      exact hasDerivAt_const t 0
    have hyr : r ≤ ‖x₀-y‖ := by
      have hy' : ¬ ‖y-x₀‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
      simpa only [norm_sub_rev] using le_of_not_gt hy'
    have hne : (x₀+t • e)-y ≠ 0 := by
      intro he
      have he' : y = x₀+t • e := (sub_eq_zero.mp he).symm
      rw [he',norm_sub_rev,add_sub_cancel_left] at hyr
      linarith [show ‖t • e‖ < r/2 from ht]
    have haff : HasDerivAt (fun t : ℝ => (x₀+t • e)-y) e t := by
      simpa using (((hasDerivAt_id t).smul_const e).const_add x₀).sub_const y
    have hd := ((hasFDerivAt_kernel hne).comp_hasDerivAt t haff).mul_const (g y)
    simpa only [_root_.smul_apply,innerSL_apply_apply,smul_eq_mul,kernelDir,Function.comp_apply] using hd
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE5} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
lemma contDiff_mul_cutoff {g ξ : E → ℝ} {s : Set E} {k : ℕ∞ω} (hs : IsOpen s)
    (hg : ContDiffOn ℝ k g s) (hξ : ContDiff ℝ k ξ) (hξs : tsupport ξ ⊆ s) :
    ContDiff ℝ k (fun y => ξ y*g y) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport ξ
  · exact hξ.contDiffAt.mul (hg.contDiffAt (hs.mem_nhds (hξs hx)))
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport ξ).isOpen_compl.mem_nhds hx] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]

omit [Nontrivial E] in
lemma rawPotential_eq_convolve (g : E → ℝ) : rawPotential g = convolve (fun y : E => ‖y‖^(2-(Module.finrank ℝ E:ℝ))) g := by
  ext x
  rw [rawPotential,convolve_def,← integral_sub_left_eq_self (fun y : E => ‖y‖^(2-(Module.finrank ℝ E:ℝ))*g (x-y)) volume x]
  simp only [sub_sub_cancel]

omit [Nontrivial E] in
lemma integrable_kernelDir_local (hn : 1 ≤ Module.finrank ℝ E) {g : E → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (e x : E) :
    Integrable (fun y => kernelDir e (x-y)*g y) := by
  have hh := (locallyIntegrable_kernelDir hn e).integrable_smul_right_of_hasCompactSupport
    (hg.comp (continuous_const.sub continuous_id)) (hc.comp_homeomorph (Homeomorph.subLeft x))
  have hi := (Measure.measurePreserving_sub_left volume x).integrable_comp hh.aestronglyMeasurable
  apply hi.mpr hh |>.congr
  exact Eventually.of_forall fun y => by simp only [Function.comp_apply,Pi.sub_apply,id_eq,sub_sub_cancel,smul_eq_mul]

lemma dir_rawPotential_local (hn : 1 ≤ Module.finrank ℝ E) {g : E → ℝ}
    (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) (e x : E) :
    dir (rawPotential g) e x = ∫ y, kernelDir e (x-y)*g y := by
  let φ : E → ℝ := fun z => g (x-z)
  have hφ : ContDiff ℝ 2 φ := hg.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hdφ (z : E) : dir φ e z = -dir g e (x-z) := by
    unfold dir φ
    have hd := (hg.differentiable (by norm_num) (x-z)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).const_sub x)
    have hfd : fderiv ℝ (fun z => g (x-z)) z = _ := hd.fderiv
    rw [hfd]
    simp
  have hh := integral_kernel_dir hn hφ hφc e
  simp_rw [hdφ,mul_neg,integral_neg] at hh
  have hh' := neg_injective hh
  rw [rawPotential_eq_convolve,dir_convolve (locallyIntegrable_newtonKernel hn) (hg.of_le (by norm_num)) hc,convolve_def,hh']
  rw [← integral_sub_left_eq_self (fun z => kernelDir e z*g (x-z)) volume x]
  simp only [sub_sub_cancel]

lemma hasLineDerivAt_rawPotential_local (hn : 1 ≤ Module.finrank ℝ E) {g : E → ℝ}
    (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) (e x : E) :
    HasLineDerivAt ℝ (rawPotential g) (∫ y, kernelDir e (x-y)*g y) x e := by
  have hd : Differentiable ℝ (rawPotential g) := by
    rw [rawPotential_eq_convolve]
    exact (contDiff_convolve (locallyIntegrable_newtonKernel hn) hg hc).differentiable (by norm_num)
  rw [← dir_rawPotential_local hn hg hc]
  exact (hd x).hasFDerivAt.hasLineDerivAt e
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE6} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma hasLineDerivAt_rawPotential (hn : 3 ≤ Module.finrank ℝ E) {g : E → ℝ} {s : Set E}
    (hg : Measurable g) (hgp : ∀ x, 0 ≤ g x) (hs : IsOpen s) (hgc : ContDiffOn ℝ 2 g s)
    (hi : ∀ x, Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y))
    {x₀ : E} (hx₀ : x₀ ∈ s) (e : E) :
    Integrable (fun y => kernelDir e (x₀-y)*g y) ∧
      HasLineDerivAt ℝ (rawPotential g) (∫ y, kernelDir e (x₀-y)*g y) x₀ e := by
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  let ξ : ContDiffBump x₀ := ⟨r/4,r/2,by linarith,by linarith⟩
  have hξs : tsupport ξ ⊆ s := by
    apply Subset.trans (by rw [ξ.tsupport_eq] : tsupport ξ ⊆ Metric.closedBall x₀ ξ.rOut)
    intro y hy
    apply hrs
    have hy' : dist y x₀ ≤ r/2 := hy
    change dist y x₀ < r
    linarith
  let g₀ : E → ℝ := fun y => ξ y*g y
  let g₁ : E → ℝ := fun y => (1-ξ y)*g y
  have hg₀c : ContDiff ℝ 2 g₀ := contDiff_mul_cutoff hs hgc ξ.contDiff hξs
  have hg₀k : HasCompactSupport g₀ := ξ.hasCompactSupport.mul_right
  have hg₁m : Measurable g₁ := (measurable_const.sub ξ.continuous.measurable).mul hg
  have hg₁p : ∀ y, 0 ≤ g₁ y := fun y => mul_nonneg (sub_nonneg.mpr (ξ.le_one (x := y))) (hgp y)
  have hi₀ (x : E) := rawPotential_integrable_cutoff hg hgp ξ.continuous.measurable
    (fun _ => ξ.nonneg) (fun _ => ξ.le_one) (hi x)
  have hi₁ (x : E) : Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*((1-ξ y)*g y)) := by
    simpa only [Pi.sub_apply] using rawPotential_integrable_cutoff hg hgp
      (measurable_const.sub ξ.continuous.measurable) (fun y => sub_nonneg.mpr (ξ.le_one (x := y)))
      (fun y => by change 1-ξ y ≤ 1; linarith [ξ.nonneg (x := y)]) (hi x)
  obtain ⟨hd₁,hfar⟩ := hasLineDerivAt_far_rawPotential hn hg₁m hg₁p (r := r/4) (by linarith)
    (by intro y hy
        have heq : ξ y = 1 := ξ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
        simp [g₁,heq]) (hi₁ x₀) e
  have hd₀ := integrable_kernelDir_local (by omega : 1 ≤ Module.finrank ℝ E) hg₀c.continuous hg₀k e x₀
  have heqD : (fun y => kernelDir e (x₀-y)*g y) =
      (fun y => kernelDir e (x₀-y)*g₀ y+kernelDir e (x₀-y)*g₁ y) := by
    funext y; dsimp [g₀,g₁]; ring
  refine ⟨?_,?_⟩
  · rw [heqD]
    exact hd₀.add hd₁
  have heq : rawPotential g = fun x => rawPotential g₀ x+rawPotential g₁ x := by
    ext x
    change (∫ y, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y) =
      (∫ y, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*(ξ y*g y)) +
      (∫ y, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*((1-ξ y)*g y))
    rw [← integral_add (hi₀ x) (hi₁ x)]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by ring
  rw [heq,heqD,integral_add hd₀ hd₁]
  exact (hasLineDerivAt_rawPotential_local (by omega) hg₀c hg₀k e x₀).add hfar
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden
open WeakPDE
lemma IsSolution.gradient_u {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    {x : Space n} (hx : x ≠ 0) (e : Space n) :
    Integrable (fun y => kernelDir e (x-y)*source v p A y) ∧
      newtonDenom n*dir u e x = ∫ y, kernelDir e (x-y)*source v p A y := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  obtain ⟨hi,hd⟩ := hasLineDerivAt_rawPotential (by simpa using h.dimension_ge_three hn)
    (measurable_source h.continuous_v p A) (source_nonneg (fun y => (h.positive_v y).le) p A)
    isOpen_compl_singleton (regular_source h.regular_v h.positive_v p A)
    (by simpa only [finrank_euclideanSpace_fin] using h.kernel_g_integrable hn) hx e
  refine ⟨hi,?_⟩
  have hu := (h.regular_u.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by norm_num)
  have hd' : HasLineDerivAt ℝ (fun y => newtonDenom n*u y) (newtonDenom n*dir u e x) x e := by
    simpa only [dir,_root_.smul_apply,smul_eq_mul] using (hu.hasFDerivAt.const_mul (newtonDenom n)).hasLineDerivAt e
  apply hd'.unique
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
  exact h.potential_u hn hq hy
end HenonLaneEmden
end
end Gradients

end OAI
