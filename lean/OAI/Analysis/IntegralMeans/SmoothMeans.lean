import OAI.Analysis.IntegralMeans.TraceBounds

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

def logDisk (z : ℂ) : ℂ := Complex.exp (z*Complex.I)

lemma logDisk_norm (z : ℂ) : ‖logDisk z‖ = Real.exp (-z.im) := by
  simp [logDisk,Complex.norm_exp]

lemma logDisk_mem_disk {z : ℂ} (hz : 0 < z.im) : logDisk z ∈ disk := by
  simp only [disk,Metric.mem_ball,dist_zero_right,logDisk_norm]
  exact Real.exp_lt_one_iff.mpr (by linarith)

lemma logDisk_analytic (z : ℂ) : AnalyticAt ℂ logDisk z := by
  exact (analyticAt_cexp).comp ((analyticAt_id.mul analyticAt_const))

lemma logDisk_injOn : InjOn logDisk {z : ℂ | -Real.pi < z.re ∧ z.re < Real.pi} := by
  intro z hz w hw h
  have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (by simpa using hz.1 : -Real.pi < (z*Complex.I).im)
    (by simpa using hz.2.le : (z*Complex.I).im ≤ Real.pi)
    (by simpa using hw.1 : -Real.pi < (w*Complex.I).im)
    (by simpa using hw.2.le : (w*Complex.I).im ≤ Real.pi) h
  exact mul_right_cancel₀ Complex.I_ne_zero he

lemma logDisk_realProd (x y : ℝ) :
    logDisk (Complex.equivRealProdCLM.symm (x,y)) = circlePoint (Real.exp (-y)) x := by
  rw [logDisk,Complex.equivRealProdCLM_symm_apply]
  have he : ((x:ℂ)+y*Complex.I)*Complex.I = (-y:ℂ)+(x:ℂ)*Complex.I := by rw [add_mul,mul_assoc,Complex.I_mul_I]; ring
  rw [he,Complex.exp_add,← Complex.ofReal_neg,← Complex.ofReal_exp]
  rfl

lemma logDisk_periodic (z : ℂ) : logDisk (z+2*Real.pi) = logDisk z := by
  simp only [logDisk,add_mul,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]

lemma logStrip_smooth_periodic_side (H : ℂ → ℝ) (y : ℝ) :
    fderiv ℝ ((H ∘ logDisk) ∘ Complex.equivRealProdCLM.symm) (-Real.pi,y) (1,0) =
      fderiv ℝ ((H ∘ logDisk) ∘ Complex.equivRealProdCLM.symm) (Real.pi,y) (1,0) := by
  let g := (H ∘ logDisk) ∘ Complex.equivRealProdCLM.symm
  have he : (fun p : ℝ × ℝ => g (p+(2*Real.pi,0))) = g := by
    ext p
    dsimp [g]
    have hz : Complex.equivRealProdCLM.symm ((p.1,p.2)+(2*Real.pi,0)) =
        Complex.equivRealProdCLM.symm p+2*Real.pi := by
      simp [Complex.equivRealProdCLM_symm_apply]
      ring
    rw [hz,logDisk_periodic]
  have hd := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1,0))
    (fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := (-Real.pi,y)) (2*Real.pi,0))
  rw [he] at hd
  have hp : (-Real.pi,y)+(2*Real.pi,0) = (Real.pi,y) := by
    ext <;> dsimp <;> ring
  simpa only [hp] using hd

lemma exp_boundary_lower {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) : y/2 ≤ 1-Real.exp (-y) := by
  have he := Real.add_one_le_exp y
  have hp := Real.exp_pos y
  have hn : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
  rw [hn]
  have hi : (Real.exp y)⁻¹ ≤ (1+y)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have hden : 0 < 1+y := by linarith
  have hf : y/2 ≤ 1-(1+y)⁻¹ := by
    rw [inv_eq_one_div]
    have hh : 1/(1+y) ≤ 1-y/2 := (div_le_iff₀ hden).mpr (by nlinarith)
    linarith
  linarith

lemma logStrip_height_bound {f : ℂ → ℂ} (hf : Schlicht f) {z : ℂ}
    (hz : 0 < z.im) (hz1 : z.im ≤ 1) :
    z.im ≤ 3*(1+‖f (logDisk z)‖^2)^(-1/4:ℝ) := by
  let y := z.im
  let r := Real.exp (-y)
  have hy : 0 < y := hz
  have hyr : r < 1 := Real.exp_lt_one_iff.mpr (by dsimp [y]; linarith)
  have hr : 0 < r := Real.exp_pos _
  have hd : 0 < 1-r := by linarith
  have hg := schlicht_growth_upper hf (logDisk_mem_disk hz)
  rw [logDisk_norm] at hg
  change ‖f (logDisk z)‖ ≤ r/(1-r)^2 at hg
  have hb : ‖f (logDisk z)‖ ≤ 4/y^2 := by
    have hyb := exp_boundary_lower hy hz1
    change y/2 ≤ 1-r at hyb
    calc
      ‖f (logDisk z)‖ ≤ r/(1-r)^2 := hg
      _ ≤ 1/(y/2)^2 := div_le_div₀ (by norm_num) hyr.le (by positivity) (by nlinarith)
      _ = 4/y^2 := by field_simp; ring
  have hy4 : y^4 ≤ 1 := pow_le_one₀ hy.le hz1
  have hs : (1+‖f (logDisk z)‖^2)*y^4 ≤ 17 := by
    have hb' : ‖f (logDisk z)‖*y^2 ≤ 4 := (le_div_iff₀ (sq_pos_of_pos hy)).mp hb
    have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ ‖f (logDisk z)‖*y^2) hb' 2
    nlinarith [hsquare]
  have hbase : 0 < 1+‖f (logDisk z)‖^2 := by positivity
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (1+‖f (logDisk z)‖^2)*y^4) hs (by norm_num : (0:ℝ) ≤ 1/4)
  rw [Real.mul_rpow (by positivity) (by positivity),← Real.rpow_natCast y 4,
    ← Real.rpow_mul hy.le] at hpow
  norm_num at hpow
  have h17 : (17:ℝ)^(1/4:ℝ) ≤ 3 := by
    calc
      (17:ℝ)^(1/4:ℝ) ≤ (81:ℝ)^(1/4:ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = 3 := by rw [show (81:ℝ) = 3^(4:ℝ) by norm_num,← Real.rpow_mul (by norm_num)]; norm_num
  have hmul : y*(1+‖f (logDisk z)‖^2)^(1/4:ℝ) ≤ 3 := by nlinarith
  have hpos := Real.rpow_pos_of_pos hbase (1/4:ℝ)
  rw [show (-1/4:ℝ) = -(1/4) by ring,Real.rpow_neg hbase.le,← div_eq_mul_inv]
  exact (le_div_iff₀ hpos).mpr hmul

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology
namespace Brennan

def bracketSq (z : ℂ) : ℝ := 1+z.re^2+z.im^2

def smoothPower (q : ℝ) (z : ℂ) : ℝ := bracketSq z ^ q

lemma bracketSq_eq (z : ℂ) : bracketSq z = 1+‖z‖^2 := by
  rw [Complex.sq_norm]
  simp [bracketSq,Complex.normSq_apply,pow_two,add_assoc]

lemma bracketSq_pos (z : ℂ) : 0 < bracketSq z := by rw [bracketSq_eq]; positivity

lemma bracketSq_contDiff (n : ℕ∞) : ContDiff ℝ n bracketSq := by
  exact (contDiff_const.add (Complex.reCLM.contDiff.pow 2)).add (Complex.imCLM.contDiff.pow 2)

lemma smoothPower_contDiff (q : ℝ) (n : ℕ∞) : ContDiff ℝ n (smoothPower q) :=
  (bracketSq_contDiff n).rpow_const_of_ne (fun z => (bracketSq_pos z).ne')

def bracketSqDeriv (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (2*z.re) • Complex.reCLM + (2*z.im) • Complex.imCLM

lemma bracketSq_hasFDerivAt (z : ℂ) : HasFDerivAt bracketSq (bracketSqDeriv z) z := by
  have h := (((Complex.reCLM.hasFDerivAt (x := z)).pow 2).const_add 1).add
    ((Complex.imCLM.hasFDerivAt (x := z)).pow 2)
  convert! h using 1
  simp [bracketSqDeriv]

lemma smoothPower_hasFDerivAt (q : ℝ) (z : ℂ) :
    HasFDerivAt (smoothPower q) ((q*bracketSq z^(q-1)) • bracketSqDeriv z) z :=
  (bracketSq_hasFDerivAt z).rpow_const (Or.inl (bracketSq_pos z).ne')

lemma bracketSqDeriv_hasFDerivAt (z : ℂ) : HasFDerivAt bracketSqDeriv
    ((ContinuousLinearMap.smulRight Complex.reCLM (2 • Complex.reCLM))+
      (ContinuousLinearMap.smulRight Complex.imCLM (2 • Complex.imCLM))) z := by
  have h := (((Complex.reCLM.hasFDerivAt (x := z)).const_mul 2).smul_const Complex.reCLM).add
    (((Complex.imCLM.hasFDerivAt (x := z)).const_mul 2).smul_const Complex.imCLM)
  convert! h using 1
  ext v w
  simp [ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

lemma smoothPower_secondReal (q : ℝ) (z u v : ℂ) :
    secondReal (smoothPower q) z u v =
      q*(q-1)*bracketSq z^(q-2)*(2*z.re*u.re+2*z.im*u.im)*(2*z.re*v.re+2*z.im*v.im)+
        q*bracketSq z^(q-1)*(2*u.re*v.re+2*u.im*v.im) := by
  have he : fderiv ℝ (smoothPower q) = fun z => (q*bracketSq z^(q-1)) • bracketSqDeriv z :=
    funext (fun z => (smoothPower_hasFDerivAt q z).fderiv)
  have hscalar := ((bracketSq_hasFDerivAt z).rpow_const (p := q-1) (Or.inl (bracketSq_pos z).ne')).const_mul q
  have hd := (hscalar.smul (bracketSqDeriv_hasFDerivAt z)).fderiv
  change fderiv ℝ (fun z => (q*bracketSq z^(q-1)) • bracketSqDeriv z) z = _ at hd
  rw [secondReal,he,hd]
  simp [bracketSqDeriv,ContinuousLinearMap.smulRight_apply,smul_eq_mul,show q-1-1=q-2 by ring]
  ring

lemma laplacian_smoothPower (q : ℝ) (z : ℂ) :
    Laplacian.laplacian (smoothPower q) z =
      4*q*bracketSq z^(q-2)*(1+q*‖z‖^2) := by
  rw [laplacian_eq_secondReal,smoothPower_secondReal,smoothPower_secondReal]
  have he : bracketSq z^(q-1) = bracketSq z^(q-2)*bracketSq z := by
    simpa only [show q-2+1=q-1 by ring,Real.rpow_one] using Real.rpow_add (bracketSq_pos z) (q-2) 1
  rw [he,Complex.sq_norm]
  simp [Complex.normSq_apply,bracketSq]
  ring

lemma laplacian_smoothPower_bounds {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (z : ℂ) :
    0 ≤ Laplacian.laplacian (smoothPower q) z ∧
      Laplacian.laplacian (smoothPower q) z ≤ 4*q*bracketSq z^(q-1) := by
  have hz := bracketSq_pos z
  rw [laplacian_smoothPower]
  constructor
  · positivity
  · have he : bracketSq z^(q-1) = bracketSq z^(q-2)*bracketSq z := by
      simpa only [show q-2+1=q-1 by ring,Real.rpow_one] using Real.rpow_add (bracketSq_pos z) (q-2) 1
    rw [he,← mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [bracketSq_eq]
    nlinarith [sq_nonneg ‖z‖]

lemma bracketSq_decay_integrable {q : ℝ} (hq : q < 1/4) :
    Integrable (fun z : ℂ => bracketSq z^(q-5/4)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 5/2-2*q)
    (by norm_num [Complex.finrank_real_complex]; linarith)
  convert! h using 1
  ext z
  rw [bracketSq_eq]
  congr 1
  ring

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma schlicht_smooth_trace {f : ℂ → ℂ} (hf : Schlicht f) {q : ℝ}
    (hq : 0 < q) (hq4 : q < 1/4) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      (∫ x in -Real.pi..Real.pi, smoothPower q (f (logDisk (x+y*Complex.I)))) ≤ C := by
  let F : ℂ → ℂ := f ∘ logDisk
  have hF (z : ℂ) (hz : 0 < z.im) : AnalyticAt ℂ F z :=
    ((hf.1.1.analyticOnNhd Metric.isOpen_ball _ (logDisk_mem_disk hz)).comp (logDisk_analytic z))
  apply periodic_conformal_trace_bounded (F := F) (ψ := smoothPower q)
    (b := fun w => bracketSq w^(q-5/4)) (K := 12*q) hF
  · intro z hz w hw he
    apply logDisk_injOn ⟨hz.1,hz.2.1⟩ ⟨hw.1,hw.2.1⟩
    exact hf.1.2 (logDisk_mem_disk hz.2.2) (logDisk_mem_disk hw.2.2) he
  · exact smoothPower_contDiff q 2
  · exact bracketSq_decay_integrable hq4
  · intro w
    exact Real.rpow_nonneg (bracketSq_pos w).le _
  · positivity
  · intro y _hy
    exact logStrip_smooth_periodic_side (smoothPower q ∘ f) y
  · intro z hz hz1
    rw [laplacian_holomorphic_comp (smoothPower_contDiff q 2).contDiffAt (hF z hz)]
    have hl := laplacian_smoothPower_bounds hq.le (by linarith) (F z)
    have hy := logStrip_height_bound hf hz hz1
    rw [← bracketSq_eq] at hy
    change z.im ≤ 3*bracketSq (F z)^(-1/4:ℝ) at hy
    constructor
    · exact mul_nonneg (sq_nonneg _) hl.1
    · calc
        _ ≤ (3*bracketSq (F z)^(-1/4:ℝ)) * (‖deriv F z‖^2*(4*q*bracketSq (F z)^(q-1))) :=
          mul_le_mul hy (mul_le_mul_of_nonneg_left hl.2 (sq_nonneg _))
            (mul_nonneg (sq_nonneg _) hl.1) (mul_nonneg (by norm_num) (Real.rpow_nonneg (bracketSq_pos _).le _))
        _ = _ := by
          have he : bracketSq (F z)^(-1/4:ℝ)*bracketSq (F z)^(q-1) = bracketSq (F z)^(q-5/4) := by
            rw [← Real.rpow_add (bracketSq_pos _)]
            congr 1
            ring
          calc
            _ = (12*q*‖deriv F z‖^2)*(bracketSq (F z)^(-1/4:ℝ)*bracketSq (F z)^(q-1)) := by ring
            _ = _ := by rw [he]

lemma continuous_circle_smoothPower {f : ℂ → ℂ} (hf : Schlicht f) (q r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1) : Continuous (fun θ => smoothPower q (f (circlePoint r θ))) := by
  apply (smoothPower_contDiff q 0).continuous.comp
  apply hf.1.1.continuousOn.comp_continuous (show Continuous (circlePoint r) from by unfold circlePoint; fun_prop)
  intro θ
  simpa only [disk,Metric.mem_ball,dist_zero_right,circlePoint_norm,abs_of_nonneg hr] using hr1

lemma schlicht_smooth_means {f : ℂ → ℂ} (hf : Schlicht f) {q : ℝ}
    (hq : 0 < q) (hq4 : q < 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r < 1 →
      (∫ θ in -Real.pi..Real.pi, smoothPower q (f (circlePoint r θ))) ≤ C := by
  obtain ⟨C,hC⟩ := schlicht_smooth_trace hf hq hq4
  refine ⟨|C|+2*Real.pi*(5:ℝ)^q+1,by positivity,fun r hr hr1 => ?_⟩
  by_cases hrh : r ≤ 1/2
  · have hb (θ : ℝ) : smoothPower q (f (circlePoint r θ)) ≤ (5:ℝ)^q := by
      have hm : circlePoint r θ ∈ disk := by
        simpa [disk,circlePoint_norm,abs_of_pos hr] using hr1
      have hg := schlicht_growth_upper hf hm
      rw [circlePoint_norm,abs_of_pos hr] at hg
      have hv : ‖f (circlePoint r θ)‖ ≤ 2 := by
        have hd : 0 < (1-r)^2 := sq_pos_of_pos (by linarith)
        have hh : r/(1-r)^2 ≤ 2 := (div_le_iff₀ hd).mpr (by nlinarith)
        exact hg.trans hh
      apply Real.rpow_le_rpow (bracketSq_pos _).le _ hq.le
      rw [bracketSq_eq]
      nlinarith [norm_nonneg (f (circlePoint r θ))]
    have hi := intervalIntegral.integral_mono_on (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos])
      ((continuous_circle_smoothPower hf q r hr.le hr1).intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume)) (fun θ _ => hb θ)
    simp only [intervalIntegral.integral_const,smul_eq_mul] at hi
    have hn := abs_nonneg C
    nlinarith
  · let y := -Real.log r
    have hy : 0 < y := neg_pos.mpr (Real.log_neg hr hr1)
    have hy1 : y ≤ 1 := by
      have hexp : Real.exp (-1) ≤ (1/2:ℝ) := by
        rw [Real.exp_neg]
        have he := Real.add_one_le_exp (1:ℝ)
        exact inv_le_comm₀ (Real.exp_pos _) (by norm_num) |>.mpr (by norm_num; linarith)
      have hlog : -1 ≤ Real.log r := (Real.le_log_iff_exp_le hr).mpr (hexp.trans (by linarith))
      dsimp [y]
      linarith
    have he (x : ℝ) : logDisk ((x:ℂ)+y*Complex.I) = circlePoint r x := by
      have hh := logDisk_realProd x y
      rw [Complex.equivRealProdCLM_symm_apply] at hh
      simpa only [y,neg_neg,Real.exp_log hr] using hh
    have hs := hC y hy hy1
    simp_rw [he] at hs
    have hc' := le_abs_self C
    have hn : 0 ≤ 2*Real.pi*(5:ℝ)^q := by positivity
    linarith

end Brennan

end

end OAI
