import Mathlib
import OAI.Geometry.Cannon.Conformal.CutoffBump

namespace OAI

section
section
section
section
section
section
section
section
section
section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
noncomputable section
noncomputable section
noncomputable section
open Set Metric MeasureTheory Filter Complex
open scoped Topology

namespace CannonPlane

lemma openMap_exists_max_on_sphere {u : ℂ → ℝ} (hu : Continuous u)
    (ho : IsOpenMap u) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ sphere c r, ∀ x ∈ closedBall c r, u x ≤ u z := by
  obtain ⟨z,hz,hmax⟩ := (isCompact_closedBall c r).exists_isMaxOn
    ⟨c,mem_closedBall_self hr.le⟩ hu.continuousOn
  refine ⟨z,?_,hmax⟩
  have hzle : dist z c ≤ r := hz
  apply mem_sphere.mpr
  by_contra he
  have hzlt : dist z c < r := lt_of_le_of_ne hzle he
  have hop : IsOpen (u '' ball c r) := ho _ isOpen_ball
  obtain ⟨ε,hε,hsub⟩ := Metric.isOpen_iff.mp hop (u z) ⟨z,hzlt,rfl⟩
  have hmem : u z+ε/2 ∈ ball (u z) ε := by
    rw [mem_ball,Real.dist_eq]
    have ha : |u z+ε/2-u z|=ε/2 := by rw [add_sub_cancel_left,abs_of_pos (by linarith)]
    rw [ha]; linarith
  obtain ⟨w,hw,hew⟩ := hsub hmem
  have hh : u w ≤ u z := hmax (ball_subset_closedBall hw)
  rw [hew] at hh
  linarith

lemma openMap_exists_min_on_sphere {u : ℂ → ℝ} (hu : Continuous u)
    (ho : IsOpenMap u) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ sphere c r, ∀ x ∈ closedBall c r, u z ≤ u x := by
  obtain ⟨z,hz,hh⟩ := openMap_exists_max_on_sphere hu.neg
    ((Homeomorph.neg ℝ).isOpenMap.comp ho) c hr
  exact ⟨z,hz,fun x hx => neg_le_neg_iff.mp (hh x hx)⟩

lemma homeomorph_disk_oscillation (F : ℂ ≃ₜ ℂ) (c : ℂ) {r L : ℝ}
    (hr : 0 < r) (hb : ∀ x ∈ sphere c r, ∀ y ∈ sphere c r, dist (F x) (F y) ≤ L) :
    ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r, dist (F x) (F y) ≤ 2*L := by
  obtain ⟨a,ha,hamax⟩ := openMap_exists_max_on_sphere (continuous_re.comp F.continuous)
    (isOpenMap_re.comp F.isOpenMap) c hr
  obtain ⟨b,hb',hbmin⟩ := openMap_exists_min_on_sphere (continuous_re.comp F.continuous)
    (isOpenMap_re.comp F.isOpenMap) c hr
  obtain ⟨d,hd,hdmax⟩ := openMap_exists_max_on_sphere (continuous_im.comp F.continuous)
    (isOpenMap_im.comp F.isOpenMap) c hr
  obtain ⟨e,he,hemin⟩ := openMap_exists_min_on_sphere (continuous_im.comp F.continuous)
    (isOpenMap_im.comp F.isOpenMap) c hr
  intro x hx y hy
  have hre : |(F x-F y).re| ≤ L := by
    have hv := (abs_re_le_norm (F a-F b)).trans (show ‖F a-F b‖ ≤ L by simpa only [dist_eq_norm] using hb a ha b hb')
    rw [abs_le] at hv ⊢
    simp only [sub_re] at hv ⊢
    have h1 := hamax x hx
    have h2 := hamax y hy
    have h3 := hbmin x hx
    have h4 := hbmin y hy
    dsimp only [Function.comp_def] at h1 h2 h3 h4
    constructor <;> linarith [hv.2]
  have him : |(F x-F y).im| ≤ L := by
    have hv := (abs_im_le_norm (F d-F e)).trans (show ‖F d-F e‖ ≤ L by simpa only [dist_eq_norm] using hb d hd e he)
    rw [abs_le] at hv ⊢
    simp only [sub_im] at hv ⊢
    have h1 := hdmax x hx
    have h2 := hdmax y hy
    have h3 := hemin x hx
    have h4 := hemin y hy
    dsimp only [Function.comp_def] at h1 h2 h3 h4
    constructor <;> linarith [hv.2]
  rw [dist_eq_norm]
  linarith [norm_le_abs_re_add_abs_im (F x-F y)]

lemma integral_sq_cauchy {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, f t)^2 ≤ (b-a)*(∫ t in a..b, (f t)^2) := by
  let aa := ∫ t in a..b, f t
  let bb := ∫ t in a..b, (f t)^2
  let m := aa/(b-a)
  have hfi := hf.intervalIntegrable (μ := volume) a b
  have hf2 : IntervalIntegrable (fun t => (f t)^2) volume a b :=
    (hf.pow 2).intervalIntegrable a b
  have he : (∫ t in a..b, (f t-m)^2)=bb-2*m*aa+m^2*(b-a) := by
    calc
      _ = ∫ t in a..b, ((f t)^2-2*m*f t+m^2) :=
        intervalIntegral.integral_congr fun _ _ => by ring
      _ = bb-2*m*aa+m^2*(b-a) := by
        rw [intervalIntegral.integral_add (hf2.sub (hfi.const_mul _)) intervalIntegrable_const,
          intervalIntegral.integral_sub hf2 (hfi.const_mul _),intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul,aa,bb]
        ring
  have hp : 0 ≤ ∫ t in a..b, (f t-m)^2 :=
    intervalIntegral.integral_nonneg hab.le (fun _ _ => sq_nonneg _)
  rw [he] at hp
  have ht : 0 < b-a := sub_pos.mpr hab
  have hid : (b-a)*(bb-2*m*aa+m^2*(b-a))=(b-a)*bb-aa^2 := by
    dsimp only [m]
    field_simp
    ring
  have h := mul_nonneg ht.le hp
  rw [hid] at h
  dsimp only [aa,bb] at h
  linarith

lemma circle_derivative_bound {F : ℂ → ℂ} (hf : ContDiff ℝ 1 F) (c : ℂ)
    {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖deriv (fun t => F (circleMap c r t)) θ‖ ≤ r*‖fderiv ℝ F (circleMap c r θ)‖ := by
  have hd := (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt θ
    (hasDerivAt_circleMap c r θ)
  change ‖deriv (F ∘ circleMap c r) θ‖ ≤ _
  rw [hd.deriv]
  apply le_trans (ContinuousLinearMap.le_opNorm _ _)
  rw [norm_mul,norm_circleMap_zero,Complex.norm_I,abs_of_nonneg hr,mul_one,mul_comm]

lemma circle_oscillation_bound {F : ℂ → ℂ} (hf : ContDiff ℝ 1 F) (c : ℂ)
    {r : ℝ} (hr : 0 < r) :
    ∀ x ∈ sphere c r, ∀ y ∈ sphere c r,
      dist (F x) (F y) ≤ r*(∫ t in (-Real.pi)..Real.pi, ‖fderiv ℝ F (circleMap c r t)‖) := by
  let g : ℝ → ℝ := fun t => r*‖fderiv ℝ F (circleMap c r t)‖
  have hg : Continuous g := continuous_const.mul
    ((hf.continuous_fderiv (by simp)).comp (continuous_circleMap c r)).norm
  have hcircle : circleMap c r '' Ioc (-Real.pi) Real.pi=sphere c r := by
    have h := (periodic_circleMap c r).image_Ioc Real.two_pi_pos (-Real.pi)
    rw [range_circleMap,abs_of_pos hr] at h
    convert h using 2; ring_nf
  intro x hx y hy
  rw [← hcircle] at hx hy
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  have hbound (a b : ℝ) (ha : a ∈ Ioc (-Real.pi) Real.pi)
      (hb : b ∈ Ioc (-Real.pi) Real.pi) (hab : a ≤ b) :
      ‖F (circleMap c r b)-F (circleMap c r a)‖ ≤ ∫ t in (-Real.pi)..Real.pi, g t := by
    apply (norm_sub_le_integral_of_norm_deriv_le_of_le hab
      (hf.continuous.comp (continuous_circleMap c r)).continuousOn
      ((hf.differentiable (by simp)).comp (differentiable_circleMap c r)).differentiableOn
      (.of_forall fun t _ => circle_derivative_bound hf c hr.le t) (hg.intervalIntegrable a b)).trans
    exact intervalIntegral.integral_mono_interval ha.1.le hab hb.2
      (.of_forall fun t => mul_nonneg hr.le (norm_nonneg _))
      (hg.intervalIntegrable _ _)
  rw [← intervalIntegral.integral_const_mul]
  change dist (F (circleMap c r a)) (F (circleMap c r b)) ≤ ∫ t in (-Real.pi)..Real.pi, g t
  rcases le_total a b with hab | hba
  · rw [dist_eq_norm, norm_sub_rev]; exact hbound a b ha hb hab
  · rw [dist_eq_norm]; exact hbound b a hb ha hba

lemma homeomorph_circle_energy (F : ℂ ≃ₜ ℂ) (hf : ContDiff ℝ 1 (F : ℂ → ℂ))
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      dist (F x) (F y)^2 ≤ 8*Real.pi*r^2*
        (∫ t in (-Real.pi)..Real.pi, ‖fderiv ℝ F (circleMap c r t)‖^2) := by
  intro x hx y hy
  have hosc := homeomorph_disk_oscillation F c hr (circle_oscillation_bound hf c hr) x hx y hy
  have hc : Continuous (fun t => ‖fderiv ℝ F (circleMap c r t)‖) :=
    ((hf.continuous_fderiv (by simp)).comp (continuous_circleMap c r)).norm
  have hcs := integral_sq_cauchy hc (neg_lt_self Real.pi_pos)
  have hn : 0 ≤ ∫ t in (-Real.pi)..Real.pi, ‖fderiv ℝ F (circleMap c r t)‖ :=
    intervalIntegral.integral_nonneg (neg_le_self Real.pi_pos.le) (fun _ _ => norm_nonneg _)
  have hs : dist (F x) (F y)^2 ≤ (2*(r*(∫ t in (-Real.pi)..Real.pi,
      ‖fderiv ℝ F (circleMap c r t)‖)))^2 := sq_le_sq₀ dist_nonneg (by positivity) |>.mpr hosc
  have hm := mul_le_mul_of_nonneg_left hcs (show 0 ≤ 4*r^2 by positivity)
  nlinarith

lemma polar_circle (p : ℝ × ℝ) : Complex.polarCoord.symm p=circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply,circleMap_zero,Complex.exp_mul_I,Complex.ofReal_cos,Complex.ofReal_sin]

lemma continuous_polar_circle : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
  simp only [circleMap]
  fun_prop

lemma disk_polar_integral_zero {g : ℂ → ℝ} (hg : Continuous g) {R : ℝ} (hR : 0 ≤ R) :
    (∫ z in closedBall (0 : ℂ) R, g z) =
      ∫ r in (0 : ℝ)..R, r*(∫ t in (-Real.pi)..Real.pi, g (circleMap 0 r t)) := by
  let A : Set (ℝ × ℝ) := Ioc 0 R ×ˢ Ioo (-Real.pi) Real.pi
  let T : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi
  let q : ℝ × ℝ → ℝ := fun p => p.1*g (circleMap 0 p.1 p.2)
  have hA : MeasurableSet A := measurableSet_Ioc.prod measurableSet_Ioo
  have hT : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Ioo
  have hq : Continuous q := continuous_fst.mul (hg.comp continuous_polar_circle)
  have hi : IntegrableOn q A :=
    (hq.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self)
  have hid (p : ℝ × ℝ) : T.indicator
      (fun p => p.1*(closedBall (0 : ℂ) R).indicator g (Complex.polarCoord.symm p)) p =
      A.indicator q p := by
    by_cases ht : p ∈ T
    · rw [Set.indicator_of_mem ht]
      have hr : 0 < p.1 := ht.1
      have hc : Complex.polarCoord.symm p ∈ closedBall (0 : ℂ) R ↔ p.1 ≤ R := by
        simp only [mem_closedBall,dist_zero_right,Complex.norm_polarCoord_symm,abs_of_pos hr]
      by_cases hle : p.1 ≤ R
      · rw [Set.indicator_of_mem (hc.mpr hle),Set.indicator_of_mem (show p ∈ A from ⟨⟨hr,hle⟩,ht.2⟩)]
        simp only [q,polar_circle]
      · rw [Set.indicator_of_notMem (not_iff_not.mpr hc |>.mpr hle),
          Set.indicator_of_notMem (show p ∉ A from fun hp => hle hp.1.2),mul_zero]
    · rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem
        (show p ∉ A from fun hp => ht ⟨hp.1.1,hp.2⟩)]
  calc
    _ = ∫ z, (closedBall (0 : ℂ) R).indicator g z := (integral_indicator measurableSet_closedBall).symm
    _ = ∫ p in T, p.1*(closedBall (0 : ℂ) R).indicator g (Complex.polarCoord.symm p) := by
      simpa only [T,smul_eq_mul,_root_.polarCoord] using
        (Complex.integral_comp_polarCoord_symm ((closedBall (0 : ℂ) R).indicator g)).symm
    _ = ∫ p, A.indicator q p := by rw [← integral_indicator hT]; exact integral_congr_ae (.of_forall hid)
    _ = ∫ p in A, q p := integral_indicator hA
    _ = ∫ r in Ioc (0 : ℝ) R, ∫ t in Ioo (-Real.pi) Real.pi, r*g (circleMap 0 r t) := by
      rw [Measure.volume_eq_prod] at hi ⊢
      exact setIntegral_prod q hi
    _ = ∫ r in (0 : ℝ)..R, r*(∫ t in (-Real.pi)..Real.pi, g (circleMap 0 r t)) := by
      rw [intervalIntegral.integral_of_le hR]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hr
      dsimp only
      rw [integral_const_mul,← integral_Ioc_eq_integral_Ioo,
        intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le)]

lemma translated_disk_integral (g : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    (∫ z in closedBall (0 : ℂ) R, g (c+z)) = ∫ z in closedBall c R, g z := by
  rw [← integral_indicator measurableSet_closedBall,← integral_indicator measurableSet_closedBall]
  calc
    _ = ∫ z, (closedBall c R).indicator g (c+z) := by
      apply integral_congr_ae
      filter_upwards [] with z
      have he : c+z ∈ closedBall c R ↔ z ∈ closedBall (0 : ℂ) R := by
        simp only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero]
      by_cases hz : z ∈ closedBall (0 : ℂ) R
      · rw [Set.indicator_of_mem hz,Set.indicator_of_mem (he.mpr hz)]
      · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem (not_iff_not.mpr he |>.mpr hz)]
    _ = _ := integral_add_left_eq_self _ c

lemma disk_polar_integral {g : ℂ → ℝ} (hg : Continuous g) (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ z in closedBall c R, g z) =
      ∫ r in (0 : ℝ)..R, r*(∫ t in (-Real.pi)..Real.pi, g (circleMap c r t)) := by
  rw [← translated_disk_integral g c R]
  have hc : Continuous (fun z : ℂ => g (c+z)) := hg.comp (continuous_const.add continuous_id)
  simpa only [circleMap,zero_add] using disk_polar_integral_zero hc hR

lemma continuous_circle_integral {g : ℂ → ℝ} (hg : Continuous g) (c : ℂ) :
    Continuous (fun r : ℝ => ∫ t in (-Real.pi)..Real.pi, g (circleMap c r t)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous _ continuous_const
  exact hg.comp (by simp only [circleMap]; fun_prop)

lemma approximate_circle_energy (F : ℂ ≃ₜ ℂ) {g : ℂ → ℂ}
    (hg : ContDiff ℝ 1 g) (c : ℂ) {r : ℝ} (hr : 0 < r)
    (x y : ℂ) (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r)
    (happ : ∀ z ∈ sphere c r, dist (F z) (g z) ≤ dist (F x) (F y)/8) :
    dist (F x) (F y)^2 ≤ 32*Real.pi*r^2*
      (∫ t in (-Real.pi)..Real.pi, ‖fderiv ℝ g (circleMap c r t)‖^2) := by
  let I := ∫ t in (-Real.pi)..Real.pi, ‖fderiv ℝ g (circleMap c r t)‖
  have hb : ∀ a ∈ sphere c r, ∀ b ∈ sphere c r,
      dist (F a) (F b) ≤ r*I+dist (F x) (F y)/4 := by
    intro a ha b hb
    have ho := circle_oscillation_bound hg c hr a ha b hb
    have ht := dist_triangle4 (F a) (g a) (g b) (F b)
    have ha' := happ a ha
    have hb' := happ b hb
    rw [dist_comm (g b) (F b)] at ht
    dsimp only [I] at *
    linarith
  have hosc := homeomorph_disk_oscillation F c hr hb x hx y hy
  have hc : Continuous (fun t => ‖fderiv ℝ g (circleMap c r t)‖) :=
    ((hg.continuous_fderiv (by simp)).comp (continuous_circleMap c r)).norm
  have hcs := integral_sq_cauchy hc (neg_lt_self Real.pi_pos)
  have hn : 0 ≤ I := intervalIntegral.integral_nonneg
    (neg_le_self Real.pi_pos.le) (fun _ _ => norm_nonneg _)
  have hd : dist (F x) (F y) ≤ 4*(r*I) := by linarith
  have hs : dist (F x) (F y)^2 ≤ (4*(r*I))^2 :=
    (sq_le_sq₀ dist_nonneg (by positivity)).mpr hd
  have hm := mul_le_mul_of_nonneg_left hcs (show 0 ≤ 16*r^2 by positivity)
  dsimp only [I] at hs
  nlinarith

lemma approximate_log_energy (F : ℂ ≃ₜ ℂ) {g : ℂ → ℂ}
    (hg : ContDiff ℝ 1 g) (c : ℂ) {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (x y : ℂ) (hx : x ∈ closedBall c s) (hy : y ∈ closedBall c s)
    (happ : ∀ z ∈ closedBall c R, dist (F z) (g z) ≤ dist (F x) (F y)/8) :
      dist (F x) (F y)^2*Real.log (R/s) ≤
        32*Real.pi*(∫ z in closedBall c R, ‖fderiv ℝ g z‖^2) := by
  let e : ℝ → ℝ := fun r => r*(∫ t in (-Real.pi)..Real.pi, ‖fderiv ℝ g (circleMap c r t)‖^2)
  have hg' : Continuous (fun z => ‖fderiv ℝ g z‖^2) := (hg.continuous_fderiv (by simp)).norm.pow 2
  have he : Continuous e := continuous_id.mul (continuous_circle_integral hg' c)
  have hi : IntervalIntegrable (fun r => dist (F x) (F y)^2/r) volume s R := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro r hr
    rw [uIcc_of_le hsR] at hr
    exact ne_of_gt (hs.trans_le hr.1)
  have hb : (∫ r in s..R, dist (F x) (F y)^2/r) ≤ ∫ r in s..R, 32*Real.pi*e r := by
    apply intervalIntegral.integral_mono_on hsR hi (he.const_mul _ |>.intervalIntegrable s R)
    intro r hr
    have hrp := hs.trans_le hr.1
    have h := approximate_circle_energy F hg c hrp x y
      (closedBall_subset_closedBall hr.1 hx) (closedBall_subset_closedBall hr.1 hy)
      (fun z hz => happ z (closedBall_subset_closedBall hr.2 (sphere_subset_closedBall hz)))
    apply (div_le_iff₀ hrp).mpr
    dsimp only [e]
    nlinarith
  have hm : (∫ r in s..R, e r) ≤ ∫ r in (0 : ℝ)..R, e r := by
    apply intervalIntegral.integral_mono_interval hs.le hsR le_rfl _ (he.intervalIntegrable _ _)
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro r hr
    exact mul_nonneg hr.1.le (intervalIntegral.integral_nonneg (neg_le_self Real.pi_pos.le)
      (fun _ _ => sq_nonneg _))
  rw [show (∫ r in s..R, dist (F x) (F y)^2/r)=dist (F x) (F y)^2*Real.log (R/s) by
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul,integral_inv_of_pos hs (hs.trans_le hsR)]
    simp only [div_eq_mul_inv]] at hb
  rw [intervalIntegral.integral_const_mul] at hb
  apply hb.trans
  rw [disk_polar_integral hg' c (hs.le.trans hsR)]
  exact mul_le_mul_of_nonneg_left hm (by positivity)
end CannonPlane

namespace CannonMetricQC
open MeasureTheory Set Metric Filter Function ContinuousLinearMap
open scoped Topology Convolution ENNReal NNReal

theorem weak_homeomorph_log_energy (F : ℂ ≃ₜ ℂ) {V W : ℂ → ℂ}
    (hVm : Measurable V) (hWm : Measurable W)
    (hV : LocallyIntegrable V volume) (hW : LocallyIntegrable W volume)
    (hVs : LocallyIntegrable (fun x => ‖V x‖^2) volume)
    (hWs : LocallyIntegrable (fun x => ‖W x‖^2) volume)
    (hv : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*V z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z 1*F z))
    (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*W z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z Complex.I*F z))
    (c : ℂ) {s R T : ℝ} (hs : 0 < s) (hsR : s ≤ R) (hRT : R < T)
    (x y : ℂ) (hx : x ∈ closedBall c s) (hy : y ∈ closedBall c s) :
    ENNReal.ofReal (dist (F x) (F y)^2*Real.log (R/s)) ≤
      ENNReal.ofReal (64*Real.pi)*(∫⁻ z in closedBall c T,
        ENNReal.ofReal (‖V z‖^2+‖W z‖^2)) := by
  by_cases he : F x=F y
  · simp [he]
  have hd : 0 < dist (F x) (F y)/8 := div_pos (dist_pos.mpr he) (by norm_num)
  have htu := tendstoLocallyUniformly_iff_forall_isCompact.mp
    (mollify_locally_uniform F.continuous) _ (isCompact_closedBall c R)
  have hu := Metric.tendstoUniformlyOn_iff.mp htu _ hd
  have hr := mollifier_radius_tendsto.eventually (gt_mem_nhds (sub_pos.mpr hRT))
  obtain ⟨n,hn,hnr⟩ := (hu.and hr).exists
  have hl := CannonPlane.approximate_log_energy F
    ((mollify_smooth F.continuous.locallyIntegrable n).of_le (by simp)) c hs hsR x y hx hy
    (fun z hz => (hn z hz).le)
  have hE := mollify_opNorm_energy F.continuous hVm hWm hV hW hVs hWs hv hw n c R
  have hm : (∫⁻ z in closedBall c (R+(mollifier n).rOut),
      ENNReal.ofReal (‖V z‖^2+‖W z‖^2)) ≤
      ∫⁻ z in closedBall c T, ENNReal.ofReal (‖V z‖^2+‖W z‖^2) :=
    lintegral_mono_set (closedBall_subset_closedBall (by linarith))
  calc
    _ ≤ ENNReal.ofReal (32*Real.pi)*
        ENNReal.ofReal (∫ z in closedBall c R, ‖fderiv ℝ (mollify F n) z‖^2) := by
      simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ 32*Real.pi)] using
        ENNReal.ofReal_le_ofReal hl
    _ ≤ ENNReal.ofReal (32*Real.pi)*(2*(∫⁻ z in closedBall c T,
        ENNReal.ofReal (‖V z‖^2+‖W z‖^2))) :=
      mul_le_mul_right (hE.trans (mul_le_mul_right hm 2)) _
    _ = _ := by
      rw [← mul_assoc,← show ENNReal.ofReal (32*Real.pi*2)=ENNReal.ofReal (32*Real.pi)*2 by
        rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_ofNat]]
      congr 2; ring
end CannonMetricQC
noncomputable section
namespace CannonMetricQC
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

lemma WeakQS.two {f : ℂ → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : WeakQS f H)
    (x y z : ℂ) (h : dist x y ≤ 2*dist x z) :
    dist (f x) (f y) ≤ H*(H+1)*dist (f x) (f z) := by
  let u := midpoint ℝ x y
  have hxu : dist x u=dist x y/2 := by simp [u,dist_left_midpoint,div_eq_mul_inv,mul_comm]
  have hux : dist u x=dist x y/2 := by rw [dist_comm,hxu]
  have huy : dist u y=dist x y/2 := by simp [u,dist_midpoint_right,div_eq_mul_inv,mul_comm]
  have h1 := hf x u z (show dist x u ≤ dist x z by rw [hxu]; linarith)
  have h2 := hf u y x (by rw [huy,hux])
  rw [dist_comm (f u) (f x)] at h2
  have h3 := dist_triangle (f x) (f u) (f y)
  have h4 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ H+1 by positivity)
  nlinarith

lemma WeakQS.four {f : ℂ → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : WeakQS f H)
    (x y z : ℂ) (h : dist x y ≤ 4*dist x z) :
    dist (f x) (f y) ≤ (H*(H+1))^2*dist (f x) (f z) := by
  let u := midpoint ℝ x y
  have hxu : dist x u=dist x y/2 := by simp [u,dist_left_midpoint,div_eq_mul_inv,mul_comm]
  have h1 := hf.two hH x y u (by rw [hxu]; linarith)
  have h2 := hf.two hH x u z (by rw [hxu]; linarith)
  exact h1.trans (by nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ H*(H+1) by positivity)])

theorem imageArea_upper_four (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (x y : ℂ) {R : ℝ} (hR : R ≤ 4*dist x y) :
    imageArea f (closedBall x R) ≤ ENNReal.ofReal (Real.pi*(H*(H+1))^4)*
      ENNReal.ofReal (dist (f x) (f y)^2) := by
  have hsub : f '' closedBall x R ⊆ closedBall (f x) ((H*(H+1))^2*dist (f x) (f y)) := by
    rintro w ⟨z,hz,rfl⟩
    rw [mem_closedBall,dist_comm]
    apply hf.four hH.le
    exact (show dist x z ≤ R by simpa only [mem_closedBall,dist_comm] using hz).trans hR
  rw [imageArea_apply f isClosed_closedBall.measurableSet]
  apply (measure_mono (μ:=volume) hsub).trans
  rw [Complex.volume_closedBall]
  have hpi : (NNReal.pi : ℝ≥0∞)=ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi,ENNReal.ofReal_coe_nnreal]
  rw [hpi,← ENNReal.ofReal_pow (by positivity),← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith
end CannonMetricQC
noncomputable section
open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

namespace CannonMetricQC

theorem measure_le_of_closedBall_le (μ ν : Measure ℂ) [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν]
    (h : ∀ x r, 0 < r → μ (closedBall x r) ≤ ν (closedBall x r)) : μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro s _
  apply (Besicovitch.vitaliFamily μ).measure_le_of_frequently_le ν
    Measure.AbsolutelyContinuous.rfl s
  intro x _
  apply (Besicovitch.tendsto_filterAt μ x).frequently
  apply Filter.Eventually.frequently
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact h x r hr

lemma locallyIntegrable_density_locallyFinite {e : ℂ → ℝ}
    (he : LocallyIntegrable e volume) (hp : ∀ x, 0 ≤ e x) :
    IsLocallyFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (e x))) where
  finiteAtNhds x := by
    refine ⟨closedBall x 1,closedBall_mem_nhds x (by norm_num),?_⟩
    rw [withDensity_apply _ isClosed_closedBall.measurableSet,
      ← ofReal_integral_eq_lintegral_ofReal (he.integrableOn_isCompact (isCompact_closedBall x 1))
        (.of_forall hp)]
    exact ENNReal.ofReal_lt_top
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Set Metric Filter Function ContinuousLinearMap
open scoped Topology Convolution ENNReal NNReal

theorem weakQS_imageArea_le_energy (F : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hF : WeakQS F H) {V W : ℂ → ℂ}
    (hVm : Measurable V) (hWm : Measurable W)
    (hV : LocallyIntegrable V volume) (hW : LocallyIntegrable W volume)
    (hVs : LocallyIntegrable (fun x => ‖V x‖^2) volume)
    (hWs : LocallyIntegrable (fun x => ‖W x‖^2) volume)
    (hv : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*V z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z 1*F z))
    (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*W z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z Complex.I*F z)) :
    imageArea F ≤ (Real.toNNReal (Real.pi*(H*(H+1))^4*(64*Real.pi/Real.log 2))) •
      volume.withDensity (fun z => ENNReal.ofReal (‖V z‖^2+‖W z‖^2)) := by
  let ν := volume.withDensity (fun z => ENNReal.ofReal (‖V z‖^2+‖W z‖^2))
  let : IsLocallyFiniteMeasure ν := locallyIntegrable_density_locallyFinite
    (hVs.add hWs) (fun z => add_nonneg (sq_nonneg _) (sq_nonneg _))
  apply measure_le_of_closedBall_le
  intro c R hR
  let y : ℂ := c+(R/4:ℝ)
  have hcy : dist c y=R/4 := by
    dsimp [y]
    rw [dist_eq_norm]
    have he : c-(c+(R/4:ℝ))=(-(R/4:ℝ):ℂ) := by push_cast; ring
    rw [he,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
  have hy : y ∈ closedBall c (R/4) := by rw [mem_closedBall,dist_comm,hcy]
  have hl := weak_homeomorph_log_energy F hVm hWm hV hW hVs hWs hv hw c
    (by positivity : 0 < R/4) (by linarith : R/4 ≤ R/2) (by linarith : R/2 < R)
    c y (mem_closedBall_self (by positivity)) hy
  have heq : R/2/(R/4)=(2:ℝ) := by field_simp; ring
  rw [heq,ENNReal.ofReal_mul (sq_nonneg _)] at hl
  have hp : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hp0 : ENNReal.ofReal (Real.log (2:ℝ)) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hle := (ENNReal.le_div_iff_mul_le (Or.inl hp0) (Or.inl ENNReal.ofReal_ne_top)).mpr hl
  have hbound : ENNReal.ofReal (dist (F c) (F y)^2) ≤
      ENNReal.ofReal (64*Real.pi/Real.log 2)*ν (closedBall c R) := by
    dsimp [ν]
    rw [withDensity_apply _ isClosed_closedBall.measurableSet,ENNReal.ofReal_div_of_pos hp]
    simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hle
  have ha := imageArea_upper_four F hH hF c y (show R ≤ 4*dist c y by rw [hcy]; linarith)
  change imageArea F (closedBall c R) ≤
    ENNReal.ofReal (Real.pi*(H*(H+1))^4*(64*Real.pi/Real.log 2))*ν (closedBall c R)
  calc
    _ ≤ ENNReal.ofReal (Real.pi*(H*(H+1))^4)*ENNReal.ofReal (dist (F c) (F y)^2) := ha
    _ ≤ ENNReal.ofReal (Real.pi*(H*(H+1))^4)*
        (ENNReal.ofReal (64*Real.pi/Real.log 2)*ν (closedBall c R)) :=
      mul_le_mul_right hbound _
    _ = _ := by rw [ENNReal.ofReal_mul (show 0 ≤ Real.pi*(H*(H+1))^4 by positivity),mul_assoc]

theorem weakQS_weakW12_imageArea_ac (F : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hF : WeakQS F H) {V W : ℂ → ℂ}
    (hVm : Measurable V) (hWm : Measurable W)
    (hV : LocallyIntegrable V volume) (hW : LocallyIntegrable W volume)
    (hVs : LocallyIntegrable (fun x => ‖V x‖^2) volume)
    (hWs : LocallyIntegrable (fun x => ‖W x‖^2) volume)
    (hv : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*V z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z 1*F z))
    (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*W z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z Complex.I*F z)) :
    imageArea F ≪ volume := by
  exact (Measure.absolutelyContinuous_of_le
    (weakQS_imageArea_le_energy F hH hF hVm hWm hV hW hVs hWs hv hw)).trans
      (Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _))
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Set Metric Filter
open scoped Topology ENNReal NNReal

lemma weakQS_full_weakW12 (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H) (hf : WeakQS f H) (v : ℂ) :
    LocallyIntegrable (fun x => fderiv ℝ (f : ℂ → ℂ) x v) volume ∧
    LocallyIntegrable (fun x => ‖fderiv ℝ (f : ℂ → ℂ) x v‖^2) volume ∧
    ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*fderiv ℝ (f : ℂ → ℂ) z v)=
        -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z v*f z) := by
  have hp (K : Set ℂ) (hK : IsCompact K) :
      IntegrableOn (fun x => fderiv ℝ (f : ℂ → ℂ) x v) K volume ∧
      IntegrableOn (fun x => ‖fderiv ℝ (f : ℂ → ℂ) x v‖^2) K volume := by
    obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mp hK.isBounded
    have hm := (weakQS_local_weakW12 f hH hf R v).1
    let : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) R)) :=
      ⟨by simpa using (isCompact_closedBall (0 : ℂ) R).measure_lt_top (μ := volume)⟩
    have hv : IntegrableOn (fun x => fderiv ℝ (f : ℂ → ℂ) x v)
        (closedBall (0 : ℂ) R) volume := MemLp.integrable (by norm_num) hm
    have hs : IntegrableOn (fun x => ‖fderiv ℝ (f : ℂ → ℂ) x v‖^2)
        (closedBall (0 : ℂ) R) volume :=
      (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
    exact ⟨hv.mono_set hR, hs.mono_set hR⟩
  refine ⟨locallyIntegrable_iff.mpr (fun K hK => (hp K hK).1),
    locallyIntegrable_iff.mpr (fun K hK => (hp K hK).2),?_⟩
  intro φ hφ
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mp hφ.isBounded
  exact (weakQS_local_weakW12 f hH hf R v).2 φ hR

theorem weakQS_imageArea_ac (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H) (hf : WeakQS f H) :
    imageArea f ≪ volume := by
  obtain ⟨hV,hVs,hv⟩ := weakQS_full_weakW12 f hH hf 1
  obtain ⟨hW,hWs,hw⟩ := weakQS_full_weakW12 f hH hf Complex.I
  exact weakQS_weakW12_imageArea_ac f hH hf
    (measurable_fderiv_apply_const ℝ (f : ℂ → ℂ) 1)
    (measurable_fderiv_apply_const ℝ (f : ℂ → ℂ) Complex.I) hV hW hVs hWs hv hw

theorem weakQS_image_null (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H) (hf : WeakQS f H)
    {S : Set ℂ} (hS : volume S=0) : volume (f '' S)=0 := by
  have ht := weakQS_imageArea_ac f hH hf
  have hz : imageArea f (toMeasurable volume S)=0 := ht (by simpa only [measure_toMeasurable] using hS)
  rw [imageArea_apply f (measurableSet_toMeasurable _ _)] at hz
  exact measure_mono_null (image_mono (subset_toMeasurable volume S)) hz
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Filter
open scoped Topology

theorem weakQS_quasiMeasurePreserving (f : ℂ ≃ₜ ℂ) {H : ℝ}
    (hH : 0 < H) (hf : WeakQS f.symm H) :
    Measure.QuasiMeasurePreserving (f : ℂ → ℂ) volume volume := by
  refine ⟨f.continuous.measurable,?_⟩
  simpa only [imageArea,Homeomorph.symm_symm] using weakQS_imageArea_ac f.symm hH hf

theorem weakQS_ae_bijective_fderiv (f : ℂ ≃ₜ ℂ) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hf : WeakQS f H) (hi : WeakQS f.symm J) :
    ∀ᵐ x : ℂ, Function.Bijective (fderiv ℝ (f : ℂ → ℂ) x) := by
  have hm := weakQS_quasiMeasurePreserving f hJ hi
  filter_upwards [weakQS_ae_differentiable f hH hf,
    hm.ae (weakQS_ae_differentiable f.symm hJ hi)] with x hx hy
  have hc := hy.hasFDerivAt.comp x hx.hasFDerivAt
  have hid : (f.symm : ℂ → ℂ) ∘ (f : ℂ → ℂ)=id := by funext z; simp
  rw [hid] at hc
  have hh := hc.unique (hasFDerivAt_id x)
  have hl : Function.LeftInverse (fderiv ℝ (f.symm : ℂ → ℂ) (f x))
      (fderiv ℝ (f : ℂ → ℂ) x) := by
    intro z
    exact congrArg (fun A : ℂ →L[ℝ] ℂ => A z) hh
  exact ⟨hl.injective,LinearMap.injective_iff_surjective.mp hl.injective⟩

theorem weakQS_ae_fderiv_comp (f g : ℂ ≃ₜ ℂ) {H J K : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hK : 0 < K)
    (hf : WeakQS f H) (hg : WeakQS g J) (hgi : WeakQS g.symm K) :
    ∀ᵐ x : ℂ, fderiv ℝ (fun z => f (g z)) x =
      (fderiv ℝ (f : ℂ → ℂ) (g x)).comp (fderiv ℝ (g : ℂ → ℂ) x) := by
  filter_upwards [weakQS_ae_differentiable g hJ hg,
    (weakQS_quasiMeasurePreserving g hK hgi).ae (weakQS_ae_differentiable f hH hf)]
      with x hx hy
  exact (hy.hasFDerivAt.comp x hx.hasFDerivAt).fderiv
end CannonMetricQC

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
