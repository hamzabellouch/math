import Mathlib
import OAI.Probability.SLELocalization.ConformalKernels

namespace OAI


/-! Conformal localization and Integrated Mesh Simple estimates. -/

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace SLEExactGauge
open Layer

lemma layer_set_measurable {F : ℂ → ℂ} (hf : DifferentiableOn ℂ F (ball 0 1)) (R : ℝ) :
    MeasurableSet {w : ℂ | ‖w‖ < 1 ∧ (1-‖w‖^2)*‖deriv F w‖ ≤ R} := by
  classical
  let f : ℂ → ℝ := fun w => diskFactor w*‖deriv F w‖
  have hc : ContinuousOn f (ball 0 1) :=
    diskFactor_smooth.continuous.continuousOn.mul (hf.deriv isOpen_ball).continuousOn.norm
  have hm : Measurable ((ball (0:ℂ) 1).piecewise f (fun _ => 0)) :=
    hc.measurable_piecewise continuousOn_const measurableSet_ball
  have he : {w : ℂ | ‖w‖ < 1 ∧ (1-‖w‖^2)*‖deriv F w‖ ≤ R} =
      ball (0:ℂ) 1 ∩ {w | (ball (0:ℂ) 1).piecewise f (fun _ => 0) w ≤ R} := by
    ext w
    by_cases hw : w ∈ ball (0:ℂ) 1
    · have hw1 := mem_ball_zero_iff.1 hw
      simp [hw,hw1,f,diskFactor]
    · have hn : ¬‖w‖ < 1 := by simpa only [mem_ball_zero_iff] using hw
      simp [hn,hw]
  rw [he]
  exact measurableSet_ball.inter (measurableSet_le hm measurable_const)

theorem conformalRadiusLayer :
    ∃ C : ℝ, 0 < C ∧ ∀ F : ℂ → ℂ,
      DifferentiableOn ℂ F (Metric.ball 0 1) → Set.InjOn F (Metric.ball 0 1) →
      ∀ R : ℝ, 0 < R →
      (∫⁻ w in {w : ℂ | ‖w‖ < 1 ∧ (1-‖w‖^2)*‖deriv F w‖ ≤ R},
        ENNReal.ofReal (Real.log (1/‖w‖)*‖deriv F w‖^2) ∂volume) ≤
      ENNReal.ofReal (C*R^2) := by
  refine ⟨4*Real.pi/Layer.layerExponent,div_pos (by positivity) layerExponent_bounds.1,?_⟩
  intro F hf hi R hR
  obtain ⟨G,h⟩ := univalent_diskPair hf hi
  let S := {w : ℂ | ‖w‖ < 1 ∧ (1-‖w‖^2)*‖deriv F w‖ ≤ R}
  let u := layerBarrier F R
  have hα := layerExponent_bounds.1
  have hC : 0 ≤ 2/Layer.layerExponent := by positivity
  have hpoint (w : ℂ) (hw : w ∈ S) :
      ENNReal.ofReal (Real.log (1/‖w‖)*‖deriv F w‖^2) ≤
      ENNReal.ofReal (2/Layer.layerExponent) * ENNReal.ofReal
        (Real.log (1/‖w‖)*(-Laplacian.laplacian u w)) := by
    have hb := h.barrier_layer hw.1 hR hw.2
    have hlog : 0 ≤ Real.log (1/‖w‖) := by
      by_cases hz : w = 0
      · simp [hz]
      · exact Real.log_nonneg ((one_le_div (norm_pos_iff.2 hz)).2 hw.1.le)
    rw [← ENNReal.ofReal_mul hC]
    apply ENNReal.ofReal_le_ofReal
    have hb' : ‖deriv F w‖^2 ≤ (2/Layer.layerExponent)*(-Laplacian.laplacian u w) := by
      have hm := mul_le_mul_of_nonneg_left hb hC
      have he : (2/Layer.layerExponent)*(Layer.layerExponent/2*‖deriv F w‖^2) = ‖deriv F w‖^2 := by
        field_simp
      rw [he] at hm
      exact hm
    nlinarith [mul_le_mul_of_nonneg_left hb' hlog]
  have hS : MeasurableSet S := layer_set_measurable hf R
  have hsub : S ⊆ ball (0:ℂ) 1 := fun w hw => mem_ball_zero_iff.2 hw.1
  have hb := superharmonic_disk_green (h.barrier_smooth R)
    (fun z _ => barrier_bounds F R z)
    (fun z hz => h.barrier_superharmonic (mem_ball_zero_iff.1 hz) R)
  calc
    _ ≤ ∫⁻ w in S, ENNReal.ofReal (2/Layer.layerExponent) *
        ENNReal.ofReal (Real.log (1/‖w‖)*(-Laplacian.laplacian u w)) :=
      setLIntegral_mono' hS hpoint
    _ ≤ ∫⁻ w in ball (0:ℂ) 1, ENNReal.ofReal (2/Layer.layerExponent) *
        ENNReal.ofReal (Real.log (1/‖w‖)*(-Laplacian.laplacian u w)) := lintegral_mono_set hsub
    _ = ENNReal.ofReal (2/Layer.layerExponent) * (∫⁻ w in ball (0:ℂ) 1,
        ENNReal.ofReal (Real.log (1/‖w‖)*(-Laplacian.laplacian u w))) := by
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2/Layer.layerExponent) * ENNReal.ofReal (2*Real.pi*R^2) :=
      mul_le_mul_right hb _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hC]
      congr 1
      ring

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace SLEExactGauge.Layer
open SlitMaps

lemma DiskPair.radius_le_omitted {U : Set ℂ} {F G : ℂ → ℂ}
    (h : DiskPair U F G) {z w : ℂ} (hz : ‖z‖ < 1) (hw : w ∉ U) :
    diskFactor z*‖deriv F z‖ ≤ (256*Real.pi)*dist (F z) w := by
  have hr := h.recenter hz
  have homit : w ∉ (F ∘ diskAuto (-z)) '' ball (0:ℂ) 1 := by
    rintro ⟨q,hq,rfl⟩
    exact hw (hr.toDomain hq)
  have hb := UnivalentDistance.omitted_value_bound hr.forward hr.injOn homit
  have hF := h.forward.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz))
  have hφ := diskAuto_hasDerivAt (show ‖-z‖ < 1 by simpa using hz) (z := (0:ℂ)) (by simp)
  have hφ0 : diskAuto (-z) 0 = z := by simp
  have he := (hφ0.symm ▸ hF.hasDerivAt).comp (0:ℂ) hφ
  have hd : deriv (F ∘ diskAuto (-z)) 0 = deriv F z*((diskFactor z:ℝ):ℂ) := by
    have hdφ := diskAuto_deriv_zero_exact hz
    have ha : (1-(starRingEnd ℂ z)*z) = ((diskFactor z:ℝ):ℂ) := by
      rw [mul_comm (starRingEnd ℂ z),Complex.mul_conj']
      simp only [diskFactor,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow]
    rw [ha] at hdφ
    simpa only [hφ0,map_neg,neg_mul_neg,mul_zero,sub_zero,one_pow,div_one,ha] using he.deriv
  rw [hd,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (diskFactor_pos hz)] at hb
  simpa only [Function.comp_apply,hφ0,dist_eq_norm,mul_comm (diskFactor z)] using hb

lemma DiskPair.radius_le_infDist {U : Set ℂ} {F G : ℂ → ℂ}
    (h : DiskPair U F G) (hne : Uᶜ.Nonempty) {z : ℂ} (hz : ‖z‖ < 1) :
    diskFactor z*‖deriv F z‖ ≤ (256*Real.pi)*infDist (F z) Uᶜ := by
  have hp : 0 < 256*Real.pi := by positivity
  rw [mul_comm (256*Real.pi),← div_le_iff₀ hp]
  apply (le_infDist hne).2
  intro w hw
  rw [div_le_iff₀ hp]
  exact (h.radius_le_omitted hz hw).trans_eq (mul_comm _ _)

lemma complexJacobian (c : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det = ‖c‖^2 := by
  simp [ContinuousLinearMap.det,LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq,Complex.normSq_eq_norm_sq]

theorem physical_boundary_layer :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set ℂ) (F G : ℂ → ℂ), DiskPair U F G → Uᶜ.Nonempty →
      ∀ R : ℝ, 0 < R →
      (∫⁻ w in {w : ℂ | w ∈ U ∧ infDist w Uᶜ ≤ R},
        ENNReal.ofReal (Real.log (1/‖G w‖))) ≤ ENNReal.ofReal (C*R^2) := by
  obtain ⟨C,hC,hbound⟩ := conformalRadiusLayer
  refine ⟨C*(256*Real.pi)^2,by positivity,?_⟩
  intro U F G h hne R hR
  let S := {z : ℂ | ‖z‖ < 1 ∧ (1-‖z‖^2)*‖deriv F z‖ ≤ (256*Real.pi)*R}
  have hS : MeasurableSet S := layer_set_measurable h.forward _
  have hsub : S ⊆ ball (0:ℂ) 1 := fun z hz => mem_ball_zero_iff.2 hz.1
  have himage : {w : ℂ | w ∈ U ∧ infDist w Uᶜ ≤ R} ⊆ F '' S := by
    intro w hw
    refine ⟨G w,⟨mem_ball_zero_iff.1 (h.toDisk hw.1),?_⟩,h.right_inv w hw.1⟩
    have hh := h.radius_le_infDist hne (mem_ball_zero_iff.1 (h.toDisk hw.1))
    rw [h.right_inv w hw.1] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hw.2 (by positivity))
  have hchange := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun z hz => ((h.forward.differentiableAt (isOpen_ball.mem_nhds (hsub hz))).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    (h.injOn.mono hsub) (fun w => ENNReal.ofReal (Real.log (1/‖G w‖)))
  calc
    _ ≤ ∫⁻ w in F '' S, ENNReal.ofReal (Real.log (1/‖G w‖)) := lintegral_mono_set himage
    _ = ∫⁻ z in S, ENNReal.ofReal (Real.log (1/‖z‖)*‖deriv F z‖^2) := by
      rw [hchange]
      apply setLIntegral_congr_fun hS
      intro z hz
      dsimp only
      rw [complexJacobian,abs_of_nonneg (sq_nonneg _),h.left_inv z (hsub hz),
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (C*((256*Real.pi)*R)^2) := hbound F h.forward h.injOn _ (by positivity)
    _ = _ := by congr 1; ring

end SLEExactGauge.Layer

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology
namespace SLEExactGauge.Mesh

def halfPlaneGreen (z w : ℂ) : ℝ := Real.log ‖(z-(starRingEnd ℂ w))/(z-w)‖

lemma hasDerivAt_log_norm {f : ℝ → ℂ} {D : ℂ} {t : ℝ}
    (hd : HasDerivAt f D t) (hn : f t ≠ 0) :
    HasDerivAt (fun u => Real.log ‖f u‖) (D/f t).re t := by
  have hh : ContDiffAt ℝ 2 (fun z : ℂ => Real.log ‖z‖) (f t) :=
    (analyticAt_id.harmonicAt_log_norm hn).1
  have hc := (hh.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hd
  have he := Layer.logNorm_fderiv (hasDerivAt_id (f t)) hn D
  apply hc.congr_deriv
  simpa only [id_eq,one_mul] using he

lemma green_eq_difference {z w : ℂ} (hn : z ≠ w) (hp : z ≠ starRingEnd ℂ w) :
    halfPlaneGreen z w = Real.log ‖z-(starRingEnd ℂ w)‖ - Real.log ‖z-w‖ := by
  rw [halfPlaneGreen,norm_div,Real.log_div (norm_ne_zero_iff.2 (sub_ne_zero.2 hp))
    (norm_ne_zero_iff.2 (sub_ne_zero.2 hn))]

lemma difference_velocity {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) (hd : z ≠ w) :
    (2/z-2/w)/(z-w) = -2/(z*w) := by
  field_simp
  ring

lemma green_velocity {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (-2/(z*(starRingEnd ℂ w))).re - (-2/(z*w)).re =
      -4*z.im/(‖z‖^2) * (w.im/(‖w‖^2)) := by
  have hzn : Complex.normSq z ≠ 0 := by
    rw [← Complex.sq_norm]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 (by intro he; simp [he] at hz))
  have hwn : Complex.normSq w ≠ 0 := by
    rw [← Complex.sq_norm]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 (by intro he; simp [he] at hw))
  rw [Complex.div_re,Complex.div_re,Complex.normSq_mul,Complex.normSq_mul,Complex.normSq_conj,
    Complex.sq_norm,Complex.sq_norm]
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.neg_re,Complex.neg_im]
  norm_num
  field_simp
  ring

theorem green_decrease {g h : ℝ → ℂ} {t u : ℝ}
    (hz : 0 < (g t).im) (hw : 0 < (h t).im) (hne : g t ≠ h t)
    (hg : HasDerivAt g (2/(g t-(u:ℂ))) t)
    (hh : HasDerivAt h (2/(h t-(u:ℂ))) t) :
    HasDerivAt (fun s => halfPlaneGreen (g s) (h s))
      (-4*(g t).im/‖g t-(u:ℂ)‖^2 * ((h t).im/‖h t-(u:ℂ)‖^2)) t := by
  have hp : g t ≠ starRingEnd ℂ (h t) := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.conj_im] at hi
    linarith
  have hc := hg.sub hh
  have hcc := hg.sub (Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t hh)
  have h₁ := hasDerivAt_log_norm hcc (sub_ne_zero.2 hp)
  have h₂ := hasDerivAt_log_norm hc (sub_ne_zero.2 hne)
  have he : (fun s => halfPlaneGreen (g s) (h s)) =ᶠ[𝓝 t]
      (fun s => Real.log ‖g s-starRingEnd ℂ (h s)‖-Real.log ‖g s-h s‖) := by
    filter_upwards [(hg.continuousAt.sub hh.continuousAt).eventually_ne (sub_ne_zero.2 hne),
      hcc.continuousAt.eventually_ne (sub_ne_zero.2 hp)] with s hs hs'
    exact green_eq_difference (sub_ne_zero.1 hs) (sub_ne_zero.1 hs')
  apply ((h₁.sub h₂).congr_of_eventuallyEq he).congr_deriv
  let z := g t-(u:ℂ)
  let w := h t-(u:ℂ)
  have hzi : 0 < z.im := by simpa [z] using hz
  have hwi : 0 < w.im := by simpa [w] using hw
  have hzn : z ≠ 0 := by intro he; simp [he] at hzi
  have hwn : w ≠ 0 := by intro he; simp [he] at hwi
  have hzw : z ≠ w := by simpa [z,w] using hne
  have hzwc : z ≠ starRingEnd ℂ w := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.conj_im] at hi
    linarith
  have hdiff : g t-h t = z-w := by dsimp [z,w]; ring
  have hdiffc : g t-starRingEnd ℂ (h t) = z-starRingEnd ℂ w := by
    simp only [z,w,map_sub,Complex.conj_ofReal]
    ring
  have hconj : starRingEnd ℂ (2/(h t-(u:ℂ))) = 2/(starRingEnd ℂ w) := by simp [w,Complex.conj_ofNat]
  change ((2/z-starRingEnd ℂ (2/w))/(g t-starRingEnd ℂ (h t))).re -
    ((2/z-2/w)/(g t-h t)).re = _
  rw [hdiff,hdiffc]
  have hconj2 : starRingEnd ℂ (2/w) = 2/(starRingEnd ℂ w) := by
    simpa only [Complex.conj_ofNat] using (map_div₀ (starRingEnd ℂ) (2:ℂ) w)
  rw [hconj2,difference_velocity hzn (by simpa using hwn) hzwc,
    difference_velocity hzn hwn hzw,green_velocity hzi hwi]
  simp [z,w]

end SLEExactGauge.Mesh

end

end

section
noncomputable section
open Set Filter Metric Function MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge.Layer

def halfToDisk (a w : ℂ) : ℂ := (w-a)/(w-starRingEnd ℂ a)

def diskToHalf (a v : ℂ) : ℂ := (a-starRingEnd ℂ a*v)/(1-v)

lemma half_den_ne {a w : ℂ} (ha : 0 < a.im) (hw : 0 < w.im) :
    w-starRingEnd ℂ a ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.sub_im,Complex.conj_im,Complex.zero_im] at hi
  linarith

lemma disk_den_ne {v : ℂ} (hv : ‖v‖ < 1) : (1:ℂ)-v ≠ 0 := by
  intro he
  have he' : v = 1 := (sub_eq_zero.1 he).symm
  simp [he'] at hv

lemma halfToDisk_maps {a w : ℂ} (ha : 0 < a.im) (hw : 0 < w.im) :
    ‖halfToDisk a w‖ < 1 := by
  have hd := half_den_ne ha hw
  have he : ‖w-starRingEnd ℂ a‖^2 - ‖w-a‖^2 = 4*w.im*a.im := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.conj_re,Complex.conj_im]
    ring
  rw [halfToDisk,norm_div,div_lt_one (norm_pos_iff.2 hd)]
  nlinarith [norm_nonneg (w-a),norm_nonneg (w-starRingEnd ℂ a),mul_pos hw ha]

lemma diskToHalf_im (a v : ℂ) :
    (diskToHalf a v).im = a.im*(1-‖v‖^2)/‖1-v‖^2 := by
  simp only [diskToHalf,Complex.div_im,Complex.sq_norm,Complex.normSq_apply,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.conj_re,
    Complex.conj_im,Complex.one_re,Complex.one_im]
  ring

lemma diskToHalf_maps {a v : ℂ} (ha : 0 < a.im) (hv : ‖v‖ < 1) :
    0 < (diskToHalf a v).im := by
  rw [diskToHalf_im]
  apply div_pos (mul_pos ha _) (sq_pos_of_ne_zero (norm_ne_zero_iff.2 (disk_den_ne hv)))
  nlinarith [norm_nonneg v]

lemma disk_half_inverse {a v : ℂ} (ha : 0 < a.im) (hv : ‖v‖ < 1) :
    halfToDisk a (diskToHalf a v) = v := by
  have h₁ := disk_den_ne hv
  have h₂ := half_den_ne ha (diskToHalf_maps ha hv)
  dsimp [halfToDisk,diskToHalf] at h₂ ⊢
  apply (div_eq_iff h₂).2
  field_simp
  ring

lemma half_disk_inverse {a w : ℂ} (ha : 0 < a.im) (hw : 0 < w.im) :
    diskToHalf a (halfToDisk a w) = w := by
  have h₁ := half_den_ne ha hw
  have h₂ := disk_den_ne (halfToDisk_maps ha hw)
  dsimp [halfToDisk,diskToHalf] at h₂ ⊢
  apply (div_eq_iff h₂).2
  field_simp
  ring

lemma halfToDisk_differentiable {a w : ℂ} (ha : 0 < a.im) (hw : 0 < w.im) :
    DifferentiableAt ℂ (halfToDisk a) w := by
  exact (differentiableAt_id.sub_const a).div (differentiableAt_id.sub_const _) (half_den_ne ha hw)

lemma diskToHalf_differentiable {a v : ℂ} (_ha : 0 < a.im) (hv : ‖v‖ < 1) :
    DifferentiableAt ℂ (diskToHalf a) v := by
  exact ((differentiableAt_id.const_mul _).const_sub a).div
    (differentiableAt_id.const_sub 1) (disk_den_ne hv)

lemma green_disk_eq (a w : ℂ) :
    Real.log (1/‖halfToDisk a w‖) = Mesh.halfPlaneGreen a w := by
  have hn : ‖w-starRingEnd ℂ a‖ = ‖a-starRingEnd ℂ w‖ := by
    rw [← norm_neg (w-starRingEnd ℂ a),neg_sub]
    rw [← Complex.norm_conj (starRingEnd ℂ a-w)]
    simp only [map_sub,starRingEnd_self_apply]
  rw [halfToDisk,norm_div,one_div_div,hn,norm_sub_rev w,Mesh.halfPlaneGreen,norm_div]

theorem halfPlane_boundary_layer :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set ℂ) (g f : ℂ → ℂ),
      IsOpen U → Uᶜ.Nonempty →
      MapsTo g U {z : ℂ | 0 < z.im} → MapsTo f {z : ℂ | 0 < z.im} U →
      (∀ z ∈ U, f (g z) = z) → (∀ z : ℂ, 0 < z.im → g (f z) = z) →
      DifferentiableOn ℂ g U → DifferentiableOn ℂ f {z : ℂ | 0 < z.im} →
      ∀ a : ℂ, 0 < a.im → ∀ R : ℝ, 0 < R →
      (∫⁻ w in {w : ℂ | w ∈ U ∧ infDist w Uᶜ ≤ R},
        ENNReal.ofReal (Mesh.halfPlaneGreen a (g w))) ≤ ENNReal.ofReal (C*R^2) := by
  obtain ⟨C,hC,hbound⟩ := physical_boundary_layer
  refine ⟨C,hC,?_⟩
  intro U g f hU hne hg hf hfg hgf hgd hfd a ha R hR
  have hH : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hpair : DiskPair U (f ∘ diskToHalf a) (halfToDisk a ∘ g) := by
    refine ⟨hU,?_,?_,?_,?_,?_,?_⟩
    · intro v hv
      exact hf (diskToHalf_maps ha (mem_ball_zero_iff.1 hv))
    · intro w hw
      exact mem_ball_zero_iff.2 (halfToDisk_maps ha (hg hw))
    · intro v hv
      dsimp only [Function.comp_apply]
      rw [hgf _ (diskToHalf_maps ha (mem_ball_zero_iff.1 hv))]
      exact disk_half_inverse ha (mem_ball_zero_iff.1 hv)
    · intro w hw
      dsimp only [Function.comp_apply]
      rw [half_disk_inverse ha (hg hw),hfg w hw]
    · intro v hv
      exact ((hfd.differentiableAt (hH.mem_nhds (diskToHalf_maps ha (mem_ball_zero_iff.1 hv)))).comp v
        (diskToHalf_differentiable ha (mem_ball_zero_iff.1 hv))).differentiableWithinAt
    · intro w hw
      exact ((halfToDisk_differentiable ha (hg hw)).comp w
        (hgd.differentiableAt (hU.mem_nhds hw))).differentiableWithinAt
  have hh := hbound U _ _ hpair hne R hR
  simpa only [Function.comp_apply,green_disk_eq] using hh

end SLEExactGauge.Layer

end

end

section
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge.Mesh

lemma green_nonneg {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    0 ≤ halfPlaneGreen z w := by
  by_cases he : z = w
  · subst w
    simp [halfPlaneGreen]
  have hn : 0 < ‖z-w‖ := norm_pos_iff.2 (sub_ne_zero.2 he)
  have hd : ‖z-starRingEnd ℂ w‖^2 - ‖z-w‖^2 = 4*z.im*w.im := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.conj_re,Complex.conj_im]
    ring
  apply Real.log_nonneg
  rw [norm_div,le_div_iff₀ hn,one_mul]
  nlinarith [norm_nonneg (z-starRingEnd ℂ w),mul_pos hz hw]

lemma green_continuousAt {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) (hne : z ≠ w) :
    ContinuousAt (fun q : ℂ × ℂ => halfPlaneGreen q.1 q.2) (z,w) := by
  apply ContinuousAt.log
  · exact (((continuous_fst.sub (Complex.continuous_conj.comp continuous_snd)).continuousAt).div
      (continuous_fst.sub continuous_snd).continuousAt (sub_ne_zero.2 hne)).norm
  · exact norm_ne_zero_iff.2 (div_ne_zero (Layer.half_den_ne hw hz) (sub_ne_zero.2 hne))

def poissonFactor (driver : ℝ → ℝ) (g : ℝ → ℂ → ℂ) (t : ℝ) (z : ℂ) : ℝ :=
  (g t z).im/‖g t z-(driver t:ℂ)‖^2

lemma poissonFactor_continuousOn {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) {T : ℝ} (hT : 0 ≤ T)
    (hU : ContinuousOn driver (Icc 0 T)) {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    ContinuousOn (fun t => poissonFactor driver g t z) (Icc 0 T) := by
  apply (Complex.continuous_im.comp_continuousOn (h.continuous_eval hT hz)).div
    (((h.continuous_eval hT hz).sub (Complex.continuous_ofReal.comp_continuousOn hU)).norm.pow 2)
  intro t ht
  exact pow_ne_zero 2 (norm_ne_zero_iff.2 (h.centered_ne_zero ht.1 (survivingDomain_mono ht.2 hz)))

lemma uniformization_injective {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) {t : ℝ} (ht : 0 ≤ t) :
    InjOn (g t) (localizationDomain γ t) := by
  rcases h with ⟨_,_,_,_,_,_,_,_,_,hfg,_,_,_,_⟩
  intro z hz w hw he
  simpa only [hfg t ht z hz,hfg t ht w hw] using congrArg (f t) he

lemma pair_integral {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hU : ContinuousOn driver (Icc 0 t)) {z w : ℂ}
    (hz : z ∈ localizationDomain γ t) (hw : w ∈ localizationDomain γ t) (hne : z ≠ w) :
    (∫ u in s..t, 4*poissonFactor driver g u z*poissonFactor driver g u w) =
      halfPlaneGreen (g s z) (g s w)-halfPlaneGreen (g t z) (g t w) := by
  have ht : 0 ≤ t := hs.trans hst
  have hsub : Icc s t ⊆ Icc 0 t := Icc_subset_Icc hs le_rfl
  have hgcont : ContinuousOn (fun u => halfPlaneGreen (g u z) (g u w)) (Icc s t) := by
    intro u hu
    have hc := (green_continuousAt (h.im_pos (hs.trans hu.1) (survivingDomain_mono hu.2 hz))
      (h.im_pos (hs.trans hu.1) (survivingDomain_mono hu.2 hw))
      (fun he => hne (uniformization_injective h (hs.trans hu.1)
        (survivingDomain_mono hu.2 hz) (survivingDomain_mono hu.2 hw) he)))
    have hp := (((h.continuous_eval ht hz).mono hsub) u hu).prodMk
      (((h.continuous_eval ht hw).mono hsub) u hu)
    exact ContinuousAt.comp_continuousWithinAt (f := fun v => (g v z,g v w)) hc hp
  have hi : IntervalIntegrable
      (fun u => -4*poissonFactor driver g u z*poissonFactor driver g u w) volume s t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hst]
    exact ((((poissonFactor_continuousOn h ht hU hz).const_mul (-4)).mul
      (poissonFactor_continuousOn h ht hU hw)).mono hsub)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hgcont
    (f' := fun u => -4*poissonFactor driver g u z*poissonFactor driver g u w)
    (fun u hu => by
      have hu0 := hs.trans_lt hu.1
      have hz' := survivingDomain_mono hu.2.le hz
      have hw' := survivingDomain_mono hu.2.le hw
      have hd := green_decrease (h.im_pos hu0.le hz') (h.im_pos hu0.le hw')
        (fun he => hne (uniformization_injective h hu0.le hz' hw' he))
        (h.hasDerivAt_eval hu0 hz') (h.hasDerivAt_eval hu0 hw')
      exact hd.congr_deriv (by dsimp [poissonFactor]; ring)) hi
  have he' : (fun u => -4*poissonFactor driver g u z*poissonFactor driver g u w) =
      (fun u => -(4*poissonFactor driver g u z*poissonFactor driver g u w)) := by funext u; ring
  rw [he',intervalIntegral.integral_neg] at he
  linarith

lemma pair_integral_le {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hU : ContinuousOn driver (Icc 0 t)) {z w : ℂ}
    (hz : z ∈ localizationDomain γ t) (hw : w ∈ localizationDomain γ t) (hne : z ≠ w) :
    (∫ u in s..t, 4*poissonFactor driver g u z*poissonFactor driver g u w) ≤
      halfPlaneGreen (g s z) (g s w) := by
  rw [pair_integral h hs hst hU hz hw hne]
  exact sub_le_self _ (green_nonneg (h.im_pos (hs.trans hst) hz) (h.im_pos (hs.trans hst) hw))

theorem loewner_boundary_layer :
    ∃ C : ℝ, 0 < C ∧ ∀ (driver : ℝ → ℝ) (γ : ℝ → ℂ) (g f : ℝ → ℂ → ℂ),
      IsLoewnerTraceUsing driver γ g f → ∀ t : ℝ, 0 ≤ t →
      ∀ z ∈ localizationDomain γ t, ∀ R : ℝ, 0 < R →
      (∫⁻ w in {w : ℂ | w ∈ localizationDomain γ t ∧ infDist w (localizationDomain γ t)ᶜ ≤ R},
        ENNReal.ofReal (halfPlaneGreen (g t z) (g t w))) ≤ ENNReal.ofReal (C*R^2) := by
  obtain ⟨C,hC,hbound⟩ := Layer.halfPlane_boundary_layer
  refine ⟨C,hC,?_⟩
  intro driver γ g f h t ht z hz R hR
  rcases h with ⟨hγ,_,_,_,_,hg,hf,hgm,hfm,hfg,hgf,_,_,_⟩
  apply hbound _ (g t) (f t) (survivingDomain_open hγ ht) _ (hgm t ht) (hfm t ht)
    (hfg t ht) (hgf t ht) (hg t ht).differentiableOn (hf t ht).differentiableOn
    (g t z) (hgm t ht hz) R hR
  refine ⟨0,?_⟩
  intro hzero
  exact (lt_irrefl (0:ℝ)) (by simpa [halfPlane] using hzero.1.1)

end SLEExactGauge.Mesh

end

end

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.PhysicalStop

lemma ofReal_cap_le (s : ℝ≥0∞) (a : ℝ) : ENNReal.ofReal (cap s a) ≤ s := by
  by_cases hs : s = ⊤
  · simp [hs]
  · rw [cap,ite_eq_right hs]
    exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans_eq (ENNReal.ofReal_toReal hs)

end SLEExactGauge.PhysicalStop

end

end

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open LoewnerCutoff LoewnerField LoewnerExit LoewnerLocalized
variable {z : ℂ} {u : ℝ} (C : Cutoff z u)

lemma first_eq_source {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω = 0)
    (hz : z ∈ halfPlane) (hu : 0 < u) {t : ℝ} (ht : t ∈ Icc 0 (C.stopTime κ B ω)) :
    iteratedDeriv 1 (field C.height_pos C.horizon.coe_nonneg (1-κ/8) (8/κ-1)
      (Real.sqrt κ) (C.paths κ B ω) z t) (B t.toNNReal ω) =
        Real.sqrt κ*(8/κ-1)*(g ω t z-(Real.sqrt κ*B t.toNNReal ω:ℂ)).re /
          ‖g ω t z-(Real.sqrt κ*B t.toNNReal ω:ℂ)‖^2 *
            ((loewnerRadius (g ω) t z)^(-(1-κ/8)) *
              (loewnerAngleSine κ (fun s => B s ω) (g ω) t z)^(8/κ-1)) := by
  have hU := C.path_eq κ B ω hc
  have h0 := C.initial_deficit_brownian κ B ω hz hu hc hb0
  have hs := source_until_stop C.height_pos C.horizon_pos hm _ z _ C.angle hU h0
  have hhi := ((deficit_nonneg_iff C.height_pos C.horizon.coe_nonneg _ z _ C.angle t).1
    (nonneg_until C.height_pos C.horizon.coe_nonneg C.horizon_pos _ z _ C.angle h0 ht)).2.1
  have hts := ht.2.trans (C.bounds κ B ω).2
  rw [first_eq,field_eq_radius_sine C.height_pos C.horizon_pos _ _ _ _ z t _ hhi (hU ⟨ht.1,hts⟩),
    radius_eq_source C.height_pos C.horizon_pos hm
      (continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn _ z _ C.angle hU h0 ht,
    sine_eq_source C.height_pos C.horizon_pos hm _ z _ C.angle hU h0 ht]
  rw [LoewnerField.height,max_eq_right hhi,← hs.2 ht]
  simp only [loewnerAngleSine,Complex.sub_re,Complex.sq_norm,Complex.normSq_apply,
    Complex.sub_im,Complex.ofReal_mul]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero,pow_two]

lemma first_le_poisson {Ω : Type*} (κ : ℝ) (hκ : 0 < κ ∧ κ ≤ 4)
    (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω = 0)
    (hz : z ∈ halfPlane) (hu : 0 < u) {e t : ℝ} (he : 0 < e) (hes : e < z.im)
    (ht : t ∈ Icc 0 (C.physicalTime κ B γ e ω)) :
    |iteratedDeriv 1 (field C.height_pos C.horizon.coe_nonneg (1-κ/8) (8/κ-1)
      (Real.sqrt κ) (C.paths κ B ω) z t) (B t.toNNReal ω)| ≤
      (Real.sqrt κ*(8/κ-1)*(e/4)^(-(1-κ/8))) *
        Mesh.poissonFactor (fun t => Real.sqrt κ*B t.toNNReal ω) (g ω) t z := by
  have hstop := ht.2.trans (C.physicalTime_bounds κ B γ e ω).2
  have hl := survivingDomain_mono hstop (C.source_live κ B ω hm hz hu hc hb0)
  let tn : ℝ≥0 := ⟨t,ht.1⟩
  have hh : (tn:ℝ≥0∞) ≤ firstLiveDistanceStop (γ ω) z e := by
    rw [← ENNReal.ofReal_coe_nnreal (p := tn)]
    exact (ENNReal.ofReal_le_ofReal ht.2).trans (PhysicalStop.ofReal_cap_le _ _)
  have hR : e/4 ≤ loewnerRadius (g ω) t z := hm.radius_ge_before_distance_stop he hes hh hl
  have ha : 1 ≤ 8/κ-1 := by
    have hh : 2 ≤ 8/κ := (le_div_iff₀ hκ.1).2 (by linarith [hκ.2])
    linarith
  rw [C.first_eq_source κ B γ g f ω hm hc hb0 hz hu ⟨ht.1,hstop⟩]
  have hz' : 0 < (g ω t z-(Real.sqrt κ*B t.toNNReal ω:ℂ)).im := by
    simpa only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,add_zero,sub_zero] using hm.im_pos ht.1 hl
  have hb := Mesh.coefficient_le_poisson hz' ha (show 0 ≤ 1-κ/8 by linarith [hκ.2])
    (Real.sqrt_nonneg κ) (show 0 < e/4 by positivity) hR
  simpa only [Mesh.poissonFactor,loewnerAngleSine,Complex.sub_im,Complex.mul_im,Complex.ofReal_im,
    mul_zero,zero_mul,add_zero,sub_zero,Complex.ofReal_mul,tn,NNReal.coe_mk] using hb

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge.Mesh

lemma poissonFactor_pos {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ∈ localizationDomain γ t) : 0 < poissonFactor driver g t z := by
  apply div_pos (h.im_pos ht hz)
  apply sq_pos_of_pos
  apply norm_pos_iff.2
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
  exact (h.im_pos ht hz).ne' hi

lemma overlap_lintegral_bound {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hU : ContinuousOn driver (Icc 0 t)) {z w : ℂ}
    (hz : z ∈ localizationDomain γ t) (hw : w ∈ localizationDomain γ t) (hne : z ≠ w)
    (b c : ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ v ∈ Icc s t, |b v| ≤ K*poissonFactor driver g v z)
    (hc : ∀ v ∈ Icc s t, |c v| ≤ K*poissonFactor driver g v w) :
    (∫⁻ v in Icc s t, ENNReal.ofReal |b v*c v|) ≤
      ENNReal.ofReal (K^2 * halfPlaneGreen (g s z) (g s w)) := by
  let F : ℝ → ℝ := fun v => 4*poissonFactor driver g v z*poissonFactor driver g v w
  have hF : ContinuousOn F (Icc s t) :=
    (((poissonFactor_continuousOn h (hs.trans hst) hU hz).const_mul 4).mul
      (poissonFactor_continuousOn h (hs.trans hst) hU hw)).mono
        (Icc_subset_Icc hs le_rfl)
  have hFp (v : ℝ) (hv : v ∈ Icc s t) : 0 ≤ F v := by
    dsimp [F]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (poissonFactor_pos h (hs.trans hv.1) (survivingDomain_mono hv.2 hz)).le)
      (poissonFactor_pos h (hs.trans hv.1) (survivingDomain_mono hv.2 hw)).le
  calc
    _ ≤ ∫⁻ v in Icc s t, ENNReal.ofReal (K^2*F v) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      apply ENNReal.ofReal_le_ofReal
      rw [abs_mul]
      have hp := mul_nonneg
        (poissonFactor_pos h (hs.trans hv.1) (survivingDomain_mono hv.2 hz)).le
        (poissonFactor_pos h (hs.trans hv.1) (survivingDomain_mono hv.2 hw)).le
      calc
        _ ≤ (K*poissonFactor driver g v z)*(K*poissonFactor driver g v w) :=
          mul_le_mul (hb v hv) (hc v hv) (abs_nonneg _) (mul_nonneg hK
            (poissonFactor_pos h (hs.trans hv.1) (survivingDomain_mono hv.2 hz)).le)
        _ ≤ K^2*F v := by dsimp [F]; nlinarith [mul_nonneg (sq_nonneg K) hp]
    _ = ENNReal.ofReal (∫ v in Icc s t, K^2*F v) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal
        ((hF.const_mul (K^2)).integrableOn_compact isCompact_Icc)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      exact mul_nonneg (sq_nonneg K) (hFp v hv)
    _ = ENNReal.ofReal (K^2*(∫ v in s..t, F v)) := by
      rw [integral_const_mul,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hst]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (pair_integral_le h hs hst hU hz hw hne) (sq_nonneg K))

lemma approached_in_boundary_layer {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (_h : IsLoewnerTraceUsing driver γ g f) {s t R : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    {w : ℂ} (hd : dist w (γ s) ≤ R) :
    infDist w (localizationDomain γ t)ᶜ ≤ R := by
  apply (infDist_le_dist_of_mem ?_).trans hd
  intro hm
  exact hm.1.2 ⟨s,⟨hs,hst⟩,rfl⟩

lemma green_symm (z w : ℂ) : halfPlaneGreen z w = halfPlaneGreen w z := by
  have hn : ‖z-starRingEnd ℂ w‖ = ‖w-starRingEnd ℂ z‖ := by
    calc
      _ = ‖starRingEnd ℂ (z-starRingEnd ℂ w)‖ := (Complex.norm_conj _).symm
      _ = ‖starRingEnd ℂ z-w‖ := by simp only [map_sub,starRingEnd_self_apply]
      _ = _ := norm_sub_rev _ _
  simp only [halfPlaneGreen,norm_div,hn,norm_sub_rev z w]

def laterGreen (g : ℝ → ℂ → ℂ) (a b : ℂ → ℝ) (z w : ℂ) : ℝ≥0∞ :=
  if a w ≤ a z ∧ a z ≤ b w then
    ENNReal.ofReal (halfPlaneGreen (g (a z) z) (g (a z) w)) else 0

lemma laterGreen_row {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) {A : Set ℂ} (hA : MeasurableSet A)
    {a b : ℂ → ℝ} {R C : ℝ} (_hR : 0 < R)
    (hstart : ∀ z ∈ A, 0 ≤ a z) (hab : ∀ z ∈ A, a z ≤ b z)
    (hlive : ∀ z ∈ A, z ∈ localizationDomain γ (b z))
    (happroach : ∀ z ∈ A, dist z (γ (a z)) ≤ R)
    (hlayer : ∀ t : ℝ, 0 ≤ t → ∀ z ∈ localizationDomain γ t,
      (∫⁻ w in {w : ℂ | w ∈ localizationDomain γ t ∧ infDist w (localizationDomain γ t)ᶜ ≤ R},
        ENNReal.ofReal (halfPlaneGreen (g t z) (g t w))) ≤ ENNReal.ofReal (C*R^2))
    {z : ℂ} (hz : z ∈ A) :
    (∫⁻ w in A, laterGreen g a b z w) ≤ ENNReal.ofReal (C*R^2) := by
  let L : Set ℂ := {w | w ∈ localizationDomain γ (a z) ∧
    infDist w (localizationDomain γ (a z))ᶜ ≤ R}
  have hLm : MeasurableSet L := (survivingDomain_open h.1 (hstart z hz)).measurableSet.inter
    (isClosed_le (continuous_infDist_pt _) continuous_const).measurableSet
  calc
    _ ≤ ∫⁻ w in A, L.indicator
        (fun w => ENNReal.ofReal (halfPlaneGreen (g (a z) z) (g (a z) w))) w := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with w hw
      unfold laterGreen
      split_ifs with horder
      · have hwL : w ∈ L := ⟨survivingDomain_mono horder.2 (hlive w hw),
          approached_in_boundary_layer h (hstart w hw) horder.1 (happroach w hw)⟩
        rw [indicator_of_mem hwL]
      · exact zero_le
    _ ≤ ∫⁻ w, L.indicator
        (fun w => ENNReal.ofReal (halfPlaneGreen (g (a z) z) (g (a z) w))) w :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ w in L, ENNReal.ofReal (halfPlaneGreen (g (a z) z) (g (a z) w)) :=
      lintegral_indicator hLm _
    _ ≤ _ := hlayer (a z) (hstart z hz) z (survivingDomain_mono (hab z hz) (hlive z hz))

lemma supported_pair_lintegral {a b : ℂ → ℝ} {B : ℝ → ℂ → ℝ} {z w : ℂ}
    (hz : ∀ t, t ∉ Icc (a z) (b z) → B t z = 0)
    (hw : ∀ t, t ∉ Icc (a w) (b w) → B t w = 0) :
    (∫⁻ t, ENNReal.ofReal |B t z*B t w|) =
      ∫⁻ t in Icc (max (a z) (a w)) (min (b z) (b w)), ENNReal.ofReal |B t z*B t w| := by
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Icc (max (a z) (a w)) (min (b z) (b w))
  · rw [indicator_of_mem ht]
  · rw [indicator_of_notMem ht]
    have hh : t ∉ Icc (a z) (b z) ∨ t ∉ Icc (a w) (b w) := by
      by_contra hn
      push Not at hn
      exact ht ⟨max_le hn.1.1 hn.2.1,le_min hn.1.2 hn.2.2⟩
    rcases hh with hh | hh <;> simp [hz t,hw t,hh]

lemma asynchronous_pair_bound {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) (hU : Continuous driver)
    {a b : ℂ → ℝ} {B : ℝ → ℂ → ℝ} {z w : ℂ} (hne : z ≠ w)
    (hz0 : 0 ≤ a z) (_hw0 : 0 ≤ a w) (_hzab : a z ≤ b z) (_hwab : a w ≤ b w)
    (hzlive : z ∈ localizationDomain γ (b z)) (hwlive : w ∈ localizationDomain γ (b w))
    (hzsup : ∀ t, t ∉ Icc (a z) (b z) → B t z = 0)
    (hwsup : ∀ t, t ∉ Icc (a w) (b w) → B t w = 0)
    {K : ℝ} (hK : 0 ≤ K)
    (hzb : ∀ t ∈ Icc (a z) (b z), |B t z| ≤ K*poissonFactor driver g t z)
    (hwb : ∀ t ∈ Icc (a w) (b w), |B t w| ≤ K*poissonFactor driver g t w) :
    (∫⁻ t, ENNReal.ofReal |B t z*B t w|) ≤
      ENNReal.ofReal (K^2) * (laterGreen g a b z w+laterGreen g a b w z) := by
  rw [supported_pair_lintegral hzsup hwsup]
  by_cases hover : max (a z) (a w) ≤ min (b z) (b w)
  · have hi := overlap_lintegral_bound h (hz0.trans (le_max_left _ _)) hover hU.continuousOn
      (survivingDomain_mono (min_le_left _ _) hzlive)
      (survivingDomain_mono (min_le_right _ _) hwlive) hne (fun t => B t z) (fun t => B t w) hK
      (fun t ht => hzb t ⟨(le_max_left _ _).trans ht.1,ht.2.trans (min_le_left _ _)⟩)
      (fun t ht => hwb t ⟨(le_max_right _ _).trans ht.1,ht.2.trans (min_le_right _ _)⟩)
    rw [ENNReal.ofReal_mul (sq_nonneg K)] at hi
    apply hi.trans
    apply mul_le_mul_right
    by_cases horder : a w ≤ a z
    · rw [max_eq_left horder]
      have hzw : a z ≤ b w := (le_max_left _ _).trans (hover.trans (min_le_right _ _))
      rw [laterGreen,ite_eq_left ⟨horder,hzw⟩]
      exact le_add_right le_rfl
    · have hwz : a z ≤ a w := (lt_of_not_ge horder).le
      rw [max_eq_right hwz]
      have hwzb : a w ≤ b z := (le_max_right _ _).trans (hover.trans (min_le_left _ _))
      have hk : halfPlaneGreen (g (a w) z) (g (a w) w) =
          halfPlaneGreen (g (a w) w) (g (a w) z) := green_symm _ _
      rw [hk]
      have hright : laterGreen g a b w z = ENNReal.ofReal (halfPlaneGreen (g (a w) w) (g (a w) z)) := by
        rw [laterGreen,ite_eq_left ⟨hwz,hwzb⟩]
      rw [← hright]
      exact le_add_left le_rfl
  · rw [Icc_eq_empty hover,Measure.restrict_empty,lintegral_zero_measure]
    exact zero_le

lemma norm_integral_sq_le_pairs {E : Type*} [MeasurableSpace E] {μ : Measure E}
    (v : E → ℝ) (hv : Measurable v) :
    ENNReal.ofReal (|∫ z, v z ∂μ|^2) ≤
      ∫⁻ z, ∫⁻ w, ENNReal.ofReal |v z*v w| ∂μ ∂μ := by
  have hn : ENNReal.ofReal |∫ z, v z ∂μ| ≤ ∫⁻ z, ENNReal.ofReal |v z| ∂μ := by
    simpa only [← ofReal_norm,Real.norm_eq_abs] using
      (enorm_integral_le_lintegral_enorm (μ := μ) v)
  rw [ENNReal.ofReal_pow (abs_nonneg _)]
  calc
    _ ≤ (∫⁻ z, ENNReal.ofReal |v z| ∂μ)^2 := pow_le_pow_left₀ zero_le hn 2
    _ = ∫⁻ z, ∫⁻ w, ENNReal.ofReal |v z*v w| ∂μ ∂μ := by
      simp_rw [abs_mul,ENNReal.ofReal_mul (abs_nonneg _)]
      rw [pow_two,lintegral_lintegral_mul hv.abs.ennreal_ofReal.aemeasurable hv.abs.ennreal_ofReal.aemeasurable]

lemma bracket_le_pair_integral {A : Set ℂ} (B : ℝ → ℂ → ℝ)
    (hB : Measurable (Function.uncurry B)) :
    (∫⁻ t, ENNReal.ofReal (|∫ z in A, B t z|^2)) ≤
      ∫⁻ z in A, ∫⁻ w in A, ∫⁻ t, ENNReal.ofReal |B t z*B t w| := by
  have hb (t : ℝ) : Measurable (B t) := hB.comp (measurable_const.prodMk measurable_id)
  have hF : Measurable (fun q : (ℝ × ℂ) × ℂ => ENNReal.ofReal |B q.1.1 q.1.2*B q.1.1 q.2|) := by
    exact ((hB.comp measurable_fst).mul
      (hB.comp (measurable_fst.fst.prodMk measurable_snd))).abs.ennreal_ofReal
  calc
    _ ≤ ∫⁻ t, ∫⁻ z in A, ∫⁻ w in A, ENNReal.ofReal |B t z*B t w| :=
      lintegral_mono (fun t => norm_integral_sq_le_pairs (B t) (hb t))
    _ = ∫⁻ z in A, ∫⁻ t, ∫⁻ w in A, ENNReal.ofReal |B t z*B t w| :=
      lintegral_lintegral_swap hF.lintegral_prod_right.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro z
      apply lintegral_lintegral_swap
      exact (((hB.comp (measurable_fst.prodMk measurable_const)).mul hB).abs.ennreal_ofReal).aemeasurable

lemma symmetric_kernel_integral {A : Set ℂ} (L : ℂ → ℂ → ℝ≥0∞)
    (hL : Measurable (Function.uncurry L)) {D : ℝ≥0∞}
    (hrow : ∀ z ∈ A, (∫⁻ w in A, L z w) ≤ D) (hA : MeasurableSet A) :
    (∫⁻ z in A, ∫⁻ w in A, L z w+L w z) ≤ 2*D*volume A := by
  have hswap := lintegral_lintegral_swap (μ := volume.restrict A) (ν := volume.restrict A) hL.aemeasurable
  have hr : (∫⁻ z in A, ∫⁻ w in A, L z w) ≤ D*volume A := by
    calc
      _ ≤ ∫⁻ z in A, D := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hA] with z hz
        exact hrow z hz
      _ = _ := by simp
  have he (z : ℂ) : (∫⁻ w in A, L z w+L w z) =
      (∫⁻ w in A, L z w)+(∫⁻ w in A, L w z) :=
    lintegral_add_left (hL.comp (measurable_const.prodMk measurable_id)) _
  simp_rw [he]
  rw [lintegral_add_left hL.lintegral_prod_right,← hswap]
  calc
    _ ≤ D*volume A+D*volume A := add_le_add hr hr
    _ = _ := by ring

theorem asynchronous_bracket_bound {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) (hU : Continuous driver)
    {A : Set ℂ} (hA : MeasurableSet A) {a b : ℂ → ℝ} {B : ℝ → ℂ → ℝ}
    (hB : Measurable (Function.uncurry B))
    (hL : Measurable (Function.uncurry (laterGreen g a b)))
    {K R C : ℝ} (hK : 0 ≤ K) (hR : 0 < R)
    (hstart : ∀ z ∈ A, 0 ≤ a z) (hab : ∀ z ∈ A, a z ≤ b z)
    (hlive : ∀ z ∈ A, z ∈ localizationDomain γ (b z))
    (happroach : ∀ z ∈ A, dist z (γ (a z)) ≤ R)
    (hsup : ∀ z ∈ A, ∀ t, t ∉ Icc (a z) (b z) → B t z = 0)
    (hcoeff : ∀ z ∈ A, ∀ t ∈ Icc (a z) (b z), |B t z| ≤ K*poissonFactor driver g t z)
    (hlayer : ∀ t : ℝ, 0 ≤ t → ∀ z ∈ localizationDomain γ t,
      (∫⁻ w in {w : ℂ | w ∈ localizationDomain γ t ∧ infDist w (localizationDomain γ t)ᶜ ≤ R},
        ENNReal.ofReal (halfPlaneGreen (g t z) (g t w))) ≤ ENNReal.ofReal (C*R^2)) :
    (∫⁻ t, ENNReal.ofReal (|∫ z in A, B t z|^2)) ≤
      2*ENNReal.ofReal (K^2)*ENNReal.ofReal (C*R^2)*volume A := by
  apply (bracket_le_pair_integral B hB).trans
  calc
    _ ≤ ∫⁻ z in A, ∫⁻ w in A,
        ENNReal.ofReal (K^2)*(laterGreen g a b z w+laterGreen g a b w z) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with z hz
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA,ae_restrict_of_ae (show ∀ᵐ w : ℂ ∂volume, w ≠ z from by rw [ae_iff]; simp)] with w hw hne
      exact asynchronous_pair_bound h hU hne.symm (hstart z hz) (hstart w hw)
        (hab z hz) (hab w hw) (hlive z hz) (hlive w hw) (hsup z hz) (hsup w hw) hK
        (hcoeff z hz) (hcoeff w hw)
    _ = ENNReal.ofReal (K^2)*(∫⁻ z in A, ∫⁻ w in A, laterGreen g a b z w+laterGreen g a b w z) := by
      simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (K^2)*(2*ENNReal.ofReal (C*R^2)*volume A) := by
      apply mul_le_mul_right
      exact symmetric_kernel_integral _ hL
        (fun z hz => laterGreen_row h hA hR hstart hab hlive happroach hlayer hz) hA
    _ = _ := by ring

theorem asynchronous_bracket_bound_with_kernel {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) (hU : Continuous driver)
    {A : Set ℂ} (hA : MeasurableSet A) {a b : ℂ → ℝ} {B : ℝ → ℂ → ℝ}
    (hB : Measurable (Function.uncurry B))
    (L : ℂ → ℂ → ℝ≥0∞) (hL : Measurable (Function.uncurry L))
    (hLeq : ∀ z ∈ A, ∀ w ∈ A, L z w = laterGreen g a b z w)
    {K R C : ℝ} (hK : 0 ≤ K) (hR : 0 < R)
    (hstart : ∀ z ∈ A, 0 ≤ a z) (hab : ∀ z ∈ A, a z ≤ b z)
    (hlive : ∀ z ∈ A, z ∈ localizationDomain γ (b z))
    (happroach : ∀ z ∈ A, dist z (γ (a z)) ≤ R)
    (hsup : ∀ z ∈ A, ∀ t, t ∉ Icc (a z) (b z) → B t z = 0)
    (hcoeff : ∀ z ∈ A, ∀ t ∈ Icc (a z) (b z), |B t z| ≤ K*poissonFactor driver g t z)
    (hlayer : ∀ t : ℝ, 0 ≤ t → ∀ z ∈ localizationDomain γ t,
      (∫⁻ w in {w : ℂ | w ∈ localizationDomain γ t ∧ infDist w (localizationDomain γ t)ᶜ ≤ R},
        ENNReal.ofReal (halfPlaneGreen (g t z) (g t w))) ≤ ENNReal.ofReal (C*R^2)) :
    (∫⁻ t, ENNReal.ofReal (|∫ z in A, B t z|^2)) ≤
      2*ENNReal.ofReal (K^2)*ENNReal.ofReal (C*R^2)*volume A := by
  apply (bracket_le_pair_integral B hB).trans
  calc
    _ ≤ ∫⁻ z in A, ∫⁻ w in A,
        ENNReal.ofReal (K^2)*(L z w+L w z) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with z hz
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA,ae_restrict_of_ae (show ∀ᵐ w : ℂ ∂volume, w ≠ z from by rw [ae_iff]; simp)] with w hw hne
      rw [hLeq z hz w hw,hLeq w hw z hz]
      exact asynchronous_pair_bound h hU hne.symm (hstart z hz) (hstart w hw)
        (hab z hz) (hab w hw) (hlive z hz) (hlive w hw) (hsup z hz) (hsup w hw) hK
        (hcoeff z hz) (hcoeff w hw)
    _ = ENNReal.ofReal (K^2)*(∫⁻ z in A, ∫⁻ w in A, L z w+L w z) := by
      simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (K^2)*(2*ENNReal.ofReal (C*R^2)*volume A) := by
      apply mul_le_mul_right
      exact symmetric_kernel_integral _ hL
        (fun z hz => by
          have he : (∫⁻ w in A, L z w) = ∫⁻ w in A, laterGreen g a b z w := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem hA] with w hw
            exact hLeq z hz w hw
          rw [he]
          exact laterGreen_row h hA hR hstart hab hlive happroach hlayer hz) hA
    _ = _ := by ring

end SLEExactGauge.Mesh

end

end

end OAI
