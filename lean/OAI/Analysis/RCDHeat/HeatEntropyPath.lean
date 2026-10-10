import Mathlib
import OAI.Analysis.RCDHeat.FisherLimit
import OAI.Analysis.RCDHeat.HopfTransport

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: HeatEntropyPath, SqrtShift, FisherSqrt, SquareClip, FisherSqrtExact. -/



namespace RegularPointCoordinates

section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem fisherInformation_aemeasurable (f : Lp ℝ 2 μ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    AEMeasurable (fisherInformation μ hQ f) (volume.restrict (Ioc a b)) := by
  apply AEMeasurable.iSup
  intro k
  exact ((regularizedFisher_intervalIntegrable μ hQ (entropyScale_pos k) f ha hab).1.aestronglyMeasurable.aemeasurable).ennreal_ofReal

 theorem heatAt_fisher_intervalIntegrable (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ) {r : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun s => (fisherInformation μ hQ f s).toReal) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  exact integrable_toReal_of_lintegral_ne_top (fisherInformation_aemeasurable μ hQ f ha hab)
    (heatAt_fisher_time_finite μ hQ p hA hB hvol f hf0 hfi hf ha hab).ne

 theorem heatAt_fisher_integral_entropy (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ) {r : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫s in a..b, (fisherInformation μ hQ f s).toReal) =
      (∫x, heatAt μ hQ a f x*Real.log (heatAt μ hQ a f x) ∂μ)-
        ∫x, heatAt μ hQ b f x*Real.log (heatAt μ hQ b f x) ∂μ := by
  have hm := fisherInformation_aemeasurable μ hQ f ha hab
  have hfin := heatAt_fisher_time_finite μ hQ p hA hB hvol f hf0 hfi hf ha hab
  rw [intervalIntegral.integral_of_le hab,integral_toReal hm (ae_lt_top' hm hfin.ne),
    heatAt_entropy_dissipation μ hQ p hA hB hvol f hf0 hfi hf ha hab,ENNReal.toReal_ofReal]
  apply sub_nonneg.mpr
  apply heatAt_entropy_mono_of_finite μ hQ f hf0 ha.le hab
    (heatAt_integrable_of_nonneg μ hQ a f hf0 hfi)
    (heatAt_integrable_of_nonneg μ hQ b f hf0 hfi)
    (heatAt_entropy_integrable μ hQ p hA hB hvol f hf0 hf ha.le)
    (heatAt_entropy_integrable μ hQ p hA hB hvol f hf0 hf (ha.le.trans hab))
  rw [heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi ha.le,
    heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi (ha.le.trans hab)]

 theorem heatAt_entropy_ae_hasDerivAt (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ) {r : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∀ᵐ s : ℝ, s ∈ Ioo a b → HasDerivAt
      (fun t => ∫x, heatAt μ hQ t f x*Real.log (heatAt μ hQ t f x) ∂μ)
      (-(fisherInformation μ hQ f s).toReal) s := by
  have hI := heatAt_fisher_intervalIntegrable μ hQ p hA hB hvol f hf0 hfi hf ha hab
  filter_upwards [hI.ae_hasDerivAt_integral] with s hs
  intro hsa
  have ht := (hs (by simpa [uIcc_of_le hab] using ⟨hsa.1.le,hsa.2.le⟩)
    a left_mem_uIcc).const_sub
      (∫x, heatAt μ hQ a f x*Real.log (heatAt μ hQ a f x) ∂μ)
  apply ht.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hsa.1 hsa.2] with t ht
  have he := heatAt_fisher_integral_entropy μ hQ p hA hB hvol f hf0 hfi hf ha ht.1.le
  linarith

omit [ProperSpace X] μ hQ in
 theorem absolutelyContinuousOnInterval_congr {F G : ℝ → ℝ} {a b : ℝ}
    (hF : AbsolutelyContinuousOnInterval F a b) (hEq : EqOn F G (uIcc a b)) :
    AbsolutelyContinuousOnInterval G a b := by
  rw [absolutelyContinuousOnInterval_iff] at hF ⊢
  intro ε hε
  obtain ⟨δ,hδ,h⟩ := hF ε hε
  refine ⟨δ,hδ,fun E hE hlen => ?_⟩
  convert h E hE hlen using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hEq (hE.1 i hi).1,hEq (hE.1 i hi).2]

 theorem heatAt_entropy_absolutelyContinuous (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ) {r : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval
      (fun t => ∫x, heatAt μ hQ t f x*Real.log (heatAt μ hQ t f x) ∂μ) a b := by
  have hI := heatAt_fisher_intervalIntegrable μ hQ p hA hB hvol f hf0 hfi hf ha hab
  have hD := hI.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ =>
      ∫x, heatAt μ hQ a f x*Real.log (heatAt μ hQ a f x) ∂μ) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  apply absolutelyContinuousOnInterval_congr (hc.sub hD)
  intro t ht
  rw [uIcc_of_le hab] at ht
  have he := heatAt_fisher_integral_entropy μ hQ p hA hB hvol f hf0 hfi hf ha ht.1
  simp only [Pi.sub_apply]
  linarith

end

 
section
open Set Filter MeasureTheory
open scoped Topology
noncomputable def sqrtShiftDeriv (ε r : ℝ) : ℝ := (2*Real.sqrt (max r 0+ε))⁻¹
noncomputable def sqrtShift (ε r : ℝ) : ℝ := ∫s in 0..r, sqrtShiftDeriv ε s
 theorem sqrtShiftDeriv_continuous {ε : ℝ} (hε : 0 < ε) : Continuous (sqrtShiftDeriv ε) := by
  unfold sqrtShiftDeriv
  apply Continuous.inv₀
  · fun_prop
  · intro r
    have hr : 0 ≤ max r 0 := le_max_right _ _
    positivity
 theorem sqrtShiftDeriv_nonneg {ε : ℝ} (hε : 0 < ε) (r : ℝ) : 0 ≤ sqrtShiftDeriv ε r := by
  unfold sqrtShiftDeriv
  positivity
 theorem sqrtShiftDeriv_le {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    |sqrtShiftDeriv ε r| ≤ (2*Real.sqrt ε)⁻¹ := by
  rw [abs_of_nonneg (sqrtShiftDeriv_nonneg hε r)]
  apply inv_anti₀ (by positivity)
  have h : ε ≤ max r 0+ε := by linarith [le_max_right r 0]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (by norm_num)
 theorem sqrtShift_hasDerivAt {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (sqrtShift ε) (sqrtShiftDeriv ε r) r := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((sqrtShiftDeriv_continuous hε).intervalIntegrable 0 r)
    ((sqrtShiftDeriv_continuous hε).stronglyMeasurableAtFilter volume (𝓝 r))
    ((sqrtShiftDeriv_continuous hε).continuousAt)
 theorem sqrtShift_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith ⟨(2*Real.sqrt ε)⁻¹,by positivity⟩ (sqrtShift ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun r => (sqrtShift_hasDerivAt hε r).differentiableAt)
  intro r
  rw [(sqrtShift_hasDerivAt hε r).deriv]
  exact_mod_cast sqrtShiftDeriv_le hε r
 theorem sqrtShift_zero (ε : ℝ) : sqrtShift ε 0 = 0 := by simp [sqrtShift]
 theorem sqrtShift_of_nonneg {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    sqrtShift ε r = Real.sqrt (r+ε)-Real.sqrt ε := by
  have hd : ∀ s ∈ Icc 0 r, HasDerivAt (fun v : ℝ => Real.sqrt (v+ε))
      (sqrtShiftDeriv ε s) s := by
    intro s hs
    simpa only [sqrtShiftDeriv,max_eq_left hs.1,one_div,id_eq] using
      ((hasDerivAt_id s).add_const ε).sqrt (ne_of_gt (add_pos_of_nonneg_of_pos hs.1 hε))
  change (∫s in 0..r, sqrtShiftDeriv ε s) = _
  simpa only [zero_add] using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le hr] using hs))
    ((sqrtShiftDeriv_continuous hε).intervalIntegrable 0 r)
 theorem sqrtShift_nonneg_le {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    0 ≤ sqrtShift ε r ∧ sqrtShift ε r ≤ Real.sqrt r := by
  rw [sqrtShift_of_nonneg hε hr]
  constructor
  · exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  · have h1 := Real.sq_sqrt (add_nonneg hr hε.le)
    have h2 := Real.sq_sqrt hr
    have h3 := Real.sq_sqrt hε.le
    have h4 := Real.sqrt_nonneg (r+ε)
    have h5 := Real.sqrt_nonneg r
    have h6 := Real.sqrt_nonneg ε
    nlinarith [mul_nonneg h5 h6]
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular] in
 theorem integrable_sqrt_memLp {f : X → ℝ} (hf : Integrable f μ) (h0 : 0 ≤ᵐ[μ] f) :
    MemLp (fun x => Real.sqrt (f x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)).mpr
  apply hf.congr
  filter_upwards [h0] with x hx
  exact (Real.sq_sqrt hx).symm

omit [ProperSpace X] [μ.Regular] in
 theorem SobolevSpace.energyLp_eq_half_slope (f : SobolevSpace μ hQ) :
    energyLp μ (SobolevSpace.toLp μ hQ f) =
      (1/2:ℝ≥0∞)*(∫⁻x, ENNReal.ofReal (SobolevSpace.minimalSlope μ hQ f x^2) ∂μ) := by
  have he : (∫⁻x, ENNReal.ofReal (SobolevSpace.minimalSlope μ hQ f x^2) ∂μ) =
      ENNReal.ofReal (‖SobolevSpace.minimalSlope μ hQ f‖^2) := by
    rw [← lintegral_enorm_sq_Lp μ]
    apply lintegral_congr
    intro x
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),sq_abs]
  rw [he,SobolevSpace.minimalSlope_norm_sq,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show (ENNReal.ofReal (2:ℝ):ℝ≥0∞) = 2 by norm_num,← mul_assoc]
  rw [ENNReal.div_mul_cancel (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞),one_mul]
  exact (ENNReal.ofReal_toReal f.property).symm

omit [μ.Regular] in
 theorem sqrtShift_gradient_energy_le (f : SobolevSpace μ hQ)
    (h0 : 0 ≤ SobolevSpace.toLp μ hQ f) {ε : ℝ} (hε : 0 < ε) :
    energyLp μ (SobolevSpace.toLp μ hQ
      (SobolevSpace.comp μ hQ (sqrtShift_lipschitz hε) (sqrtShift_zero ε) f)) ≤
      (1/8:ℝ≥0∞)*(∫⁻x, ENNReal.ofReal (SobolevSpace.minimalSlope μ hQ f x^2)/
        ENNReal.ofReal (SobolevSpace.toLp μ hQ f x) ∂μ) := by
  let g := SobolevSpace.comp μ hQ (sqrtShift_lipschitz hε) (sqrtShift_zero ε) f
  have hchain := SobolevSpace.minimalSlope_comp_C1 μ hQ f (sqrtShift_lipschitz hε)
    (sqrtShift_zero ε) (sqrtShiftDeriv_continuous hε) (sqrtShift_hasDerivAt hε)
    ⟨(2*Real.sqrt ε)⁻¹,by positivity⟩ (sqrtShiftDeriv_le hε)
  rw [SobolevSpace.energyLp_eq_half_slope]
  have hle : (∫⁻x, ENNReal.ofReal (SobolevSpace.minimalSlope μ hQ g x^2) ∂μ) ≤
      (1/4:ℝ≥0∞)*(∫⁻x, ENNReal.ofReal (SobolevSpace.minimalSlope μ hQ f x^2)/
        ENNReal.ofReal (SobolevSpace.toLp μ hQ f x) ∂μ) := by
    rw [← lintegral_const_mul' _ _ (by norm_num : (1/4:ℝ≥0∞) ≠ ∞)]
    apply lintegral_mono_ae
    filter_upwards [hchain,(Lp.coeFn_nonneg _).mpr h0] with x hc hx
    change 0 ≤ SobolevSpace.toLp μ hQ f x at hx
    rw [hc,abs_of_nonneg (sqrtShiftDeriv_nonneg hε _)]
    have hden : 0 < SobolevSpace.toLp μ hQ f x+ε := add_pos_of_nonneg_of_pos hx hε
    have he : (sqrtShiftDeriv ε (SobolevSpace.toLp μ hQ f x)*SobolevSpace.minimalSlope μ hQ f x)^2 =
        SobolevSpace.minimalSlope μ hQ f x^2 / (4*(SobolevSpace.toLp μ hQ f x+ε)) := by
      dsimp [sqrtShiftDeriv]
      rw [max_eq_left hx]
      have hs := Real.sq_sqrt hden.le
      have hs0 := (Real.sqrt_pos.mpr hden).ne'
      field_simp
      nlinarith
    rw [he,ENNReal.ofReal_div_of_pos (by positivity)]
    calc
      _ ≤ ENNReal.ofReal (SobolevSpace.minimalSlope μ hQ f x^2)/
          ENNReal.ofReal (4*SobolevSpace.toLp μ hQ f x) :=
        ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal (by linarith)) _
      _ = _ := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
        norm_num only [ENNReal.ofReal_ofNat]
        rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        simp only [div_eq_mul_inv,one_mul]
        ac_rfl
  calc
    _ ≤ (1/2:ℝ≥0∞)*((1/4:ℝ≥0∞)*_) := mul_le_mul' le_rfl hle
    _ = _ := by
      rw [← mul_assoc]
      congr 1
      simp only [div_eq_mul_inv,one_mul]
      rw [← ENNReal.mul_inv (Or.inl (by norm_num : (2:ℝ≥0∞) ≠ 0))
        (Or.inl (by norm_num : (2:ℝ≥0∞) ≠ ∞))]
      norm_num

omit [μ.Regular] in
 theorem SobolevSpace.sqrt_energy_le (f : SobolevSpace μ hQ)
    (h0 : 0 ≤ SobolevSpace.toLp μ hQ f) (hfi : Integrable (SobolevSpace.toLp μ hQ f) μ) :
    energyLp μ ((integrable_sqrt_memLp μ hfi ((Lp.coeFn_nonneg _).mpr h0)).toLp
      (fun x => Real.sqrt (SobolevSpace.toLp μ hQ f x))) ≤
      (1/8:ℝ≥0∞)*(∫⁻x, ENNReal.ofReal (SobolevSpace.minimalSlope μ hQ f x^2)/
        ENNReal.ofReal (SobolevSpace.toLp μ hQ f x) ∂μ) := by
  let g (k : ℕ) := SobolevSpace.comp μ hQ (sqrtShift_lipschitz (entropyScale_pos k))
    (sqrtShift_zero (entropyScale k)) f
  have hm (k : ℕ) : MemLp (fun x => sqrtShift (entropyScale k) (SobolevSpace.toLp μ hQ f x)) 2 μ :=
    (Lp.memLp (SobolevSpace.toLp μ hQ (g k))).ae_eq
      (SobolevSpace.comp_coe μ hQ (sqrtShift_lipschitz (entropyScale_pos k))
        (sqrtShift_zero (entropyScale k)) f)
  have he (k : ℕ) : (hm k).toLp _ = SobolevSpace.toLp μ hQ (g k) := by
    apply Lp.ext
    exact (hm k).coeFn_toLp.trans
      (SobolevSpace.comp_coe μ hQ (sqrtShift_lipschitz (entropyScale_pos k))
        (sqrtShift_zero (entropyScale k)) f).symm
  have ht := L2Differentiation.toLp_tendsto_of_dominated μ hm
    (integrable_sqrt_memLp μ hfi ((Lp.coeFn_nonneg _).mpr h0))
    (SobolevSpace.toLp μ hQ f) hfi (Eventually.of_forall fun k => ?_)
    (show ∀ᵐ x ∂μ, Tendsto (fun k => sqrtShift (entropyScale k) (SobolevSpace.toLp μ hQ f x))
      atTop (𝓝 (Real.sqrt (SobolevSpace.toLp μ hQ f x))) from ?_)
  · simp only [he] at ht
    apply (energyLp_le_liminf μ ht).trans
    exact liminf_le_of_frequently_le
      (Eventually.frequently (Eventually.of_forall fun k => sqrtShift_gradient_energy_le μ hQ f h0 (entropyScale_pos k)))
      (by isBoundedDefault)
  · filter_upwards [(Lp.coeFn_nonneg _).mpr h0] with x hx
    change 0 ≤ SobolevSpace.toLp μ hQ f x at hx
    obtain ⟨hl,hu⟩ := sqrtShift_nonneg_le (entropyScale_pos k) hx
    nlinarith [Real.sq_sqrt hx,Real.sqrt_nonneg (SobolevSpace.toLp μ hQ f x)]
  · filter_upwards [(Lp.coeFn_nonneg _).mpr h0] with x hx
    change 0 ≤ SobolevSpace.toLp μ hQ f x at hx
    simp only [sqrtShift_of_nonneg (entropyScale_pos _) hx]
    have he0 := entropyScale_tendsto.mono_right nhdsWithin_le_nhds
    have h1 := Real.continuous_sqrt.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := SobolevSpace.toLp μ hQ f x)).add he0)
    have h2 := Real.continuous_sqrt.continuousAt.tendsto.comp he0
    simpa only [Function.comp_def,add_zero,Real.sqrt_zero,sub_zero] using h1.sub h2

end

 
section
open Set Filter MeasureTheory
open scoped Topology
noncomputable def squareClipDeriv (R s : ℝ) : ℝ := 2*max (-R) (min s R)
noncomputable def squareClip (R s : ℝ) : ℝ := ∫r in 0..s, squareClipDeriv R r
 theorem squareClipDeriv_continuous (R : ℝ) : Continuous (squareClipDeriv R) := by
  unfold squareClipDeriv
  fun_prop
 theorem squareClipDeriv_bound {R : ℝ} (hR : 0 ≤ R) (s : ℝ) : |squareClipDeriv R s| ≤ 2*R := by
  rw [squareClipDeriv,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_right _ _)⟩
 theorem squareClip_hasDerivAt (R s : ℝ) : HasDerivAt (squareClip R) (squareClipDeriv R s) s := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((squareClipDeriv_continuous R).intervalIntegrable 0 s)
    ((squareClipDeriv_continuous R).stronglyMeasurableAtFilter volume (𝓝 s))
    ((squareClipDeriv_continuous R).continuousAt)
 theorem squareClip_lipschitz {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith ⟨2*R,by positivity⟩ (squareClip R) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun s => (squareClip_hasDerivAt R s).differentiableAt)
  intro s
  rw [(squareClip_hasDerivAt R s).deriv]
  exact_mod_cast squareClipDeriv_bound hR s
 theorem squareClip_zero (R : ℝ) : squareClip R 0 = 0 := by simp [squareClip]
 theorem squareClipDeriv_eq {R s : ℝ} (hs : |s| ≤ R) : squareClipDeriv R s = 2*s := by
  unfold squareClipDeriv
  rw [min_eq_left (abs_le.mp hs).2,max_eq_right (abs_le.mp hs).1]
 theorem squareClip_eq {R s : ℝ} (hs : |s| ≤ R) : squareClip R s = s^2 := by
  have hR : 0 ≤ R := (abs_nonneg _).trans hs
  have hd : ∀ r ∈ uIcc 0 s, HasDerivAt (fun v : ℝ => v^2) (squareClipDeriv R r) r := by
    intro r hr
    have hrb : r ∈ Icc (-R) R :=
      uIcc_subset_Icc ⟨by linarith,hR⟩ (abs_le.mp hs) hr
    rw [squareClipDeriv_eq (abs_le.mpr hrb)]
    convert! (hasDerivAt_pow 2 r) using 1; norm_num
  simpa only [squareClip,zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((squareClipDeriv_continuous R).intervalIntegrable 0 s)
end

 
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.fisher_eq_of_sqrt (f g : SobolevSpace μ hQ)
    (h0 : 0 ≤ SobolevSpace.toLp μ hQ f) {C : ℝ} (_hC : 0 ≤ C)
    (hfC : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ f x ≤ C)
    (hg : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ g x = Real.sqrt (SobolevSpace.toLp μ hQ f x)) :
    (∫⁻x, ENNReal.ofReal (SobolevSpace.minimalSlope μ hQ f x^2)/
      ENNReal.ofReal (SobolevSpace.toLp μ hQ f x) ∂μ) =
        8*energyLp μ (SobolevSpace.toLp μ hQ g) := by
  let R := Real.sqrt C
  have hR : 0 ≤ R := Real.sqrt_nonneg C
  have hgR : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ R := by
    filter_upwards [hg,hfC] with x hx hc
    rw [hx,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt hc
  have he : SobolevSpace.comp μ hQ (squareClip_lipschitz hR) (squareClip_zero R) g = f := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [SobolevSpace.comp_coe μ hQ (squareClip_lipschitz hR) (squareClip_zero R) g,
      hg,hgR,(Lp.coeFn_nonneg _).mpr h0] with x he hg hR h0
    change SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ (squareClip_lipschitz ‹_›) (squareClip_zero R) g) x = _
    rw [he]
    change squareClip R (SobolevSpace.toLp μ hQ g x) = SobolevSpace.toLp μ hQ f x
    rw [squareClip_eq hR,hg,Real.sq_sqrt h0]
  have hchain := SobolevSpace.minimalSlope_comp_C1 μ hQ g (squareClip_lipschitz hR)
    (squareClip_zero R) (squareClipDeriv_continuous R) (squareClip_hasDerivAt R)
    ⟨2*R,by positivity⟩ (squareClipDeriv_bound hR)
  rw [he] at hchain
  have hi : (∫⁻x, ENNReal.ofReal (SobolevSpace.minimalSlope μ hQ f x^2)/
      ENNReal.ofReal (SobolevSpace.toLp μ hQ f x) ∂μ) =
      4*(∫⁻x, ENNReal.ofReal (SobolevSpace.minimalSlope μ hQ g x^2) ∂μ) := by
    rw [← lintegral_const_mul' _ _ (by norm_num : (4:ℝ≥0∞) ≠ ∞)]
    apply lintegral_congr_ae
    filter_upwards [hchain,hg,hgR,(Lp.coeFn_nonneg _).mpr h0,
      SobolevSpace.minimalSlope_zero_on_zero μ hQ g] with x hc hx hR h0 hz
    change 0 ≤ SobolevSpace.toLp μ hQ f x at h0
    rw [squareClipDeriv_eq hR,hx,abs_of_nonneg (by positivity)] at hc
    by_cases hfz : SobolevSpace.toLp μ hQ f x = 0
    · have hgz : SobolevSpace.toLp μ hQ g x = 0 := by rw [hx,hfz,Real.sqrt_zero]
      have hgz := hz hgz
      rw [hfz,Real.sqrt_zero,mul_zero,zero_mul] at hc
      simp [hc,hfz,hgz]
    · have hfp : 0 < SobolevSpace.toLp μ hQ f x := lt_of_le_of_ne h0 (Ne.symm hfz)
      rw [← ENNReal.ofReal_div_of_pos hfp]
      calc
        _ = ENNReal.ofReal (4*SobolevSpace.minimalSlope μ hQ g x^2) := by
          congr 1
          rw [hc,mul_pow,mul_pow,Real.sq_sqrt h0]
          field_simp
          ring
        _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num
  rw [hi,SobolevSpace.energyLp_eq_half_slope]
  rw [← mul_assoc]
  congr 1
  symm
  rw [show (8:ℝ≥0∞) = 4*2 by norm_num,mul_assoc]
  rw [div_eq_mul_inv,one_mul,ENNReal.mul_inv_cancel (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞),mul_one]

 theorem SobolevSpace.fisher_eq_eight_sqrt_energy (f : SobolevSpace μ hQ)
    (h0 : 0 ≤ SobolevSpace.toLp μ hQ f) (hfi : Integrable (SobolevSpace.toLp μ hQ f) μ)
    {C : ℝ} (hC : 0 ≤ C) (hfC : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ f x ≤ C) :
    (∫⁻x, ENNReal.ofReal (SobolevSpace.minimalSlope μ hQ f x^2)/
      ENNReal.ofReal (SobolevSpace.toLp μ hQ f x) ∂μ) =
        8*energyLp μ ((integrable_sqrt_memLp μ hfi ((Lp.coeFn_nonneg _).mpr h0)).toLp
          (fun x => Real.sqrt (SobolevSpace.toLp μ hQ f x))) := by
  let hm := integrable_sqrt_memLp μ hfi ((Lp.coeFn_nonneg _).mpr h0)
  let v := hm.toLp (fun x => Real.sqrt (SobolevSpace.toLp μ hQ f x))
  by_cases hv : energyLp μ v ≠ ∞
  · exact SobolevSpace.fisher_eq_of_sqrt μ hQ f ⟨v,hv⟩ h0 hC hfC hm.coeFn_toLp
  · have hv : energyLp μ v = ∞ := not_ne_iff.mp hv
    have hl := SobolevSpace.sqrt_energy_le μ hQ f h0 hfi
    change energyLp μ v ≤ _ at hl
    rw [hv] at hl
    have hi : (∫⁻x, ENNReal.ofReal (SobolevSpace.minimalSlope μ hQ f x^2)/
        ENNReal.ofReal (SobolevSpace.toLp μ hQ f x) ∂μ) = ∞ := by
      by_contra hfin
      exact (ne_of_lt (ENNReal.mul_lt_top (by finiteness) (lt_top_iff_ne_top.mpr hfin))) (top_unique hl)
    change _ = 8*energyLp μ v
    rw [hi,hv]
    norm_num

end RegularPointCoordinates

end OAI
