import OAI.Geometry.KahlerSplitting.MetricBounds

namespace OAI

section
noncomputable section
open scoped Manifold ContDiff
open Set
noncomputable section
open Set Topology Filter Metric
noncomputable section
open Set Metric

noncomputable section
open Set Metric Filter Topology
namespace UniversalCoverSplitting
variable {M E : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem chart_trapping_on_interval (e : OpenPartialHomeomorph M E)
    {c : E} {R L T : ℝ} (_hR : 0 < R) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (he : closedBall c R ⊆ e.target) {γ : ℝ → M}
    (hγ : ContinuousOn γ (Icc 0 T))
    (hzero : γ 0 ∈ e.source ∧ dist (e (γ 0)) c < R - L * T)
    (hder : ∀ t ∈ Icc 0 T, γ t ∈ e.symm '' closedBall c R →
      ∃ D : E, HasDerivWithinAt (e ∘ γ) D (Icc 0 T) t ∧ ‖D‖ ≤ L) :
    ∀ t ∈ Icc 0 T, γ t ∈ e.source ∧ e (γ t) ∈ ball c R := by
  let K := e.symm '' closedBall c R
  have hK : IsCompact K := (isCompact_closedBall c R).image_of_continuousOn
    (e.continuousOn_symm.mono he)
  have hKs : K ⊆ e.source := by
    rintro _ ⟨z,hz,rfl⟩
    exact e.map_target (he hz)
  have hKe : ∀ x ∈ K, e x ∈ closedBall c R := by
    rintro _ ⟨z,hz,rfl⟩
    simpa only [e.right_inv (he hz)] using hz
  have h0 : γ 0 ∈ K := by
    refine ⟨e (γ 0),?_,e.left_inv hzero.1⟩
    exact (hzero.2.trans_le (sub_le_self _ (mul_nonneg hL hT))).le
  have hA : IsClosed ((γ ⁻¹' K) ∩ Icc 0 T) :=
    by simpa [inter_comm] using hγ.preimage_isClosed_of_isClosed isClosed_Icc hK.isClosed
  have control (t : ℝ) (ht : t ∈ Icc 0 T)
      (hst : Icc 0 t ⊆ γ ⁻¹' K) : e (γ t) ∈ ball c R := by
    have hbound : ‖e (γ t) - e (γ 0)‖ ≤ L * t := by
      choose! D hD hDL using fun s (hs : s ∈ Icc 0 t) ↦
        hder s ⟨hs.1,hs.2.trans ht.2⟩ (hst hs)
      have hh := norm_image_sub_le_of_norm_deriv_le_segment'
        (fun s hs ↦ (hD s hs).mono (Icc_subset_Icc_right ht.2))
        (fun s hs ↦ hDL s (Ico_subset_Icc_self hs)) t (by exact ⟨ht.1,le_rfl⟩)
      simpa using hh
    change dist (e (γ t)) c < R
    have hdist : dist (e (γ t)) (e (γ 0)) ≤ L * t := by
      simpa [dist_eq_norm] using hbound
    have hm := mul_le_mul_of_nonneg_left ht.2 hL
    calc
      dist (e (γ t)) c ≤ dist (e (γ t)) (e (γ 0)) + dist (e (γ 0)) c := dist_triangle _ _ _
      _ ≤ L * T + dist (e (γ 0)) c := add_le_add (hdist.trans hm) le_rfl
      _ < R := by linarith [hzero.2]
  have hall : Icc 0 T ⊆ γ ⁻¹' K := by
    apply hA.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset h0
    intro t ht hst
    have hsrc := hKs (hst (right_mem_Icc.mpr ht.1))
    have hball := control t (Ico_subset_Icc_self ht) hst
    have hopen : IsOpen (e.source ∩ e ⁻¹' ball c R) := e.isOpen_inter_preimage isOpen_ball
    have hsub : e.source ∩ e ⁻¹' ball c R ⊆ K := by
      intro x hx
      exact ⟨e x,ball_subset_closedBall hx.2,e.left_inv hx.1⟩
    exact (((hγ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)).mono Ioi_subset_Ici_self)
      (mem_of_superset (hopen.mem_nhds ⟨hsrc,hball⟩) hsub)
  intro t ht
  exact ⟨hKs (hall ht),control t ht (fun s hs ↦ hall ⟨hs.1,hs.2.trans ht.2⟩)⟩

section ComplexDisk
variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem chart_trapping_on_disk (e : OpenPartialHomeomorph M E)
    {c : E} {R L r : ℝ} (hR : 0 < R) (hL : 0 ≤ L) (_hr : 0 ≤ r)
    (he : closedBall c R ⊆ e.target) {h : ℂ → M}
    (hc : ContinuousOn h (closedBall 0 r))
    (hzero : h 0 ∈ e.source ∧ dist (e (h 0)) c < R - L * r)
    (hder : ∀ z ∈ closedBall 0 r, h z ∈ e.symm '' closedBall c R →
      DifferentiableAt ℂ (e ∘ h) z ∧ ‖fderiv ℂ (e ∘ h) z‖ ≤ L) :
    ∀ z ∈ closedBall 0 r, h z ∈ e.source ∧ e (h z) ∈ ball c R := by
  intro z hz
  have hz' : ‖z‖ ≤ r := by simpa using hz
  have hmem (t : ℝ) (ht : t ∈ Icc 0 1) : t • z ∈ closedBall 0 r := by
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans hz'
  have hγ : ContinuousOn (fun t : ℝ ↦ h (t • z)) (Icc 0 1) :=
    hc.comp (continuous_id.smul continuous_const).continuousOn hmem
  have hinit : h ((0 : ℝ) • z) ∈ e.source ∧ dist (e (h ((0 : ℝ) • z))) c < R - (L * ‖z‖) * 1 := by
    simp only [zero_smul,mul_one]
    refine ⟨hzero.1,hzero.2.trans_le ?_⟩
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hz' hL) R
  have htrap := chart_trapping_on_interval e hR (mul_nonneg hL (norm_nonneg z)) zero_le_one
    he hγ hinit (fun t ht hk ↦ ?_) 1 (by norm_num)
  · simpa using htrap
  obtain ⟨hd,hb⟩ := hder (t • z) (hmem t ht) hk
  refine ⟨fderiv ℂ (e ∘ h) (t • z) z,?_,?_⟩
  · simpa only [Function.comp_def,id_eq,one_smul,ContinuousLinearMap.coe_restrictScalars'] using
      ((hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
        ((hasDerivAt_id t).smul_const z)).hasDerivWithinAt (s := Icc 0 1)
  · exact ((fderiv ℂ (e ∘ h) (t • z)).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg z))

end ComplexDisk
end UniversalCoverSplitting

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped Interval
namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem norm_circleAverage_sq_le {F : ℂ → E} {c : ℂ} {R : ℝ}
    (hF : ContinuousOn F (sphere c |R|)) :
    ‖Real.circleAverage F c R‖ ^ 2 ≤ Real.circleAverage (fun z ↦ ‖F z‖ ^ 2) c R := by
  have hc : Continuous (fun θ : ℝ ↦ F (circleMap c R θ)) :=
    hF.comp_continuous (continuous_circleMap c R) (fun θ ↦ circleMap_mem_sphere' c R θ)
  have hg : ConvexOn ℝ (univ : Set E) (fun v ↦ ‖v‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ ↦ norm_nonneg _) 2
  rw [Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]
  apply hg.map_set_average_le (continuous_norm.pow 2).continuousOn isClosed_univ
  · simp [Real.volume_uIoc, Real.pi_pos]
  · rw [Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  · exact Filter.Eventually.of_forall (fun _ ↦ mem_univ _)
  · exact (hc.intervalIntegrable _ _).def'
  · exact ((hc.norm.pow 2).intervalIntegrable _ _).def'

theorem norm_sq_le_circleAverage {F : ℂ → E} {c : ℂ} {R : ℝ}
    (hF : DiffContOnCl ℂ F (ball c |R|)) :
    ‖F c‖ ^ 2 ≤ Real.circleAverage (fun z ↦ ‖F z‖ ^ 2) c R := by
  by_cases hR : R = 0
  · simp [hR]
  rw [← hF.circleAverage]
  exact norm_circleAverage_sq_le (hF.2.mono (by
    rw [closure_ball _ (abs_ne_zero.mpr hR)]
    exact sphere_subset_closedBall))

def polarEnergy (F : ℂ → E) (c : ℂ) (R : ℝ) : ℝ :=
  2 * Real.pi * ∫ r in 0..R, r * Real.circleAverage (fun z ↦ ‖F z‖ ^ 2) c r

theorem norm_sq_mul_diskArea_le_polarEnergy {F : ℂ → E} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hF : DifferentiableOn ℂ F (closedBall c R)) :
    Real.pi * R ^ 2 * ‖F c‖ ^ 2 ≤ polarEnergy F c R := by
  have hc : ContinuousOn (Real.circleAverage (fun z ↦ ‖F z‖ ^ 2) c) (Icc 0 R) := by
    apply Real.ContinuousOn.circleAverage
    · exact (hF.continuousOn.norm.pow 2).mono (fun z hz ↦ by
        simpa only [mem_closedBall, dist_eq_norm] using hz.2)
    · exact fun _ hr ↦ hr.1
  have hi : IntervalIntegrable (fun r ↦ r * Real.circleAverage (fun z ↦ ‖F z‖ ^ 2) c r)
      volume 0 R := (continuousOn_id.mul hc).intervalIntegrable_of_Icc hR
  have hle : (∫ r in 0..R, r * ‖F c‖ ^ 2) ≤
      ∫ r in 0..R, r * Real.circleAverage (fun z ↦ ‖F z‖ ^ 2) c r := by
    apply intervalIntegral.integral_mono_on hR ((continuous_id.mul continuous_const).intervalIntegrable _ _) hi
    intro r hr
    apply mul_le_mul_of_nonneg_left _ hr.1
    apply norm_sq_le_circleAverage
    apply hF.diffContOnCl_ball
    rw [abs_of_nonneg hr.1]
    exact closedBall_subset_closedBall hr.2
  have heq : (∫ r in (0 : ℝ)..R, r * ‖F c‖ ^ 2) = R ^ 2 / 2 * ‖F c‖ ^ 2 := by
    rw [intervalIntegral.integral_mul_const, integral_id]
    ring
  rw [heq] at hle
  have hh := mul_le_mul_of_nonneg_left hle (show 0 ≤ 2 * Real.pi by positivity)
  unfold polarEnergy
  nlinarith

end UniversalCoverSplitting
noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped Interval
namespace UniversalCoverSplitting

lemma polar_symm_circle (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply]
  simp only [circleMap, zero_add, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

theorem disk_integral_eq_polar {f : ℂ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ContinuousOn f (closedBall 0 R)) :
    (∫ z in ball (0 : ℂ) R, f z) =
      2 * Real.pi * ∫ r in 0..R, r * Real.circleAverage f 0 r := by
  let G : ℝ × ℝ → ℝ := fun p ↦ p.1 * f (Complex.polarCoord.symm p)
  have htarget : Complex.polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi :=
    Complex.polarCoord_target
  have heq : (∫ z in ball (0 : ℂ) R, f z) =
      ∫ p in (Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi), G p := by
    rw [← integral_indicator measurableSet_ball,
      ← Complex.integral_comp_polarCoord_symm]
    change (∫ p in Complex.polarCoord.target, p.1 • (ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p)) = _
    have hi : (∫ p in Complex.polarCoord.target,
        p.1 • (ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p)) =
        ∫ p in Complex.polarCoord.target, {p : ℝ × ℝ | p.1 < R}.indicator G p := by
      apply setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
      intro p hp
      rw [htarget] at hp
      have hm : Complex.polarCoord.symm p ∈ ball (0 : ℂ) R ↔ p.1 < R := by
        simp only [mem_ball, dist_zero_right]
        rw [Complex.norm_polarCoord_symm,abs_of_pos (show 0 < p.1 from hp.1)]
      change p.1 • (ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p) = _
      by_cases h : p.1 < R
      · rw [indicator_of_mem (hm.mpr h),indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.1 < R} from h)]
        rfl
      · rw [indicator_of_notMem (mt hm.mp h),indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.1 < R} from h),smul_zero]
    rw [hi,setIntegral_indicator (isOpen_lt continuous_fst continuous_const).measurableSet]
    have hs : Complex.polarCoord.target ∩ {p : ℝ × ℝ | p.1 < R} =
        Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi := by
      rw [htarget]
      ext p
      simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioi, mem_Ioo]
      tauto
    rw [hs]
  have hGc : ContinuousOn G (Icc 0 R ×ˢ Icc (-Real.pi) Real.pi) := by
    apply continuousOn_fst.mul (hf.comp _ _)
    · have hh : Continuous (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p) := by
        simp_rw [Complex.polarCoord_symm_apply]
        fun_prop
      exact hh.continuousOn
    · intro p hp
      simp only [mem_closedBall,dist_zero_right,Complex.norm_polarCoord_symm,
        abs_of_nonneg hp.1.1]
      exact hp.1.2
  have hGi : IntegrableOn G (Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi) :=
    (hGc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [heq,MeasureTheory.Measure.volume_eq_prod]
  rw [setIntegral_prod G (by simpa only [← MeasureTheory.Measure.volume_eq_prod] using hGi)]
  have hi (r : ℝ) : (∫ θ in Ioo (-Real.pi) Real.pi, G (r,θ)) =
      2 * Real.pi * (r * Real.circleAverage f 0 r) := by
    have ha := Real.circleAverage_eq_integral_add (f := f) (c := (0 : ℂ)) (R := r) (-Real.pi)
    have hpi : 2 * Real.pi + -Real.pi = Real.pi := by ring
    change Real.circleAverage f 0 r = (2 * Real.pi)⁻¹ •
      (∫ θ in (0:ℝ)..2*Real.pi, (fun t ↦ f (circleMap 0 r t)) (θ + -Real.pi)) at ha
    rw [intervalIntegral.integral_comp_add_right (fun t ↦ f (circleMap 0 r t)), zero_add, hpi] at ha
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      integral_Ioc_eq_integral_Ioo] at ha
    simp only [smul_eq_mul] at ha
    unfold G
    simp_rw [polar_symm_circle]
    rw [integral_const_mul]
    rw [ha]
    field_simp
  simp_rw [hi]
  rw [integral_const_mul,intervalIntegral.integral_of_le hR,integral_Ioc_eq_integral_Ioo]

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set MeasureTheory Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem norm_sq_mul_diskArea_le_integral {F : ℂ → E} {R : ℝ}
    (hR : 0 ≤ R) (hF : DifferentiableOn ℂ F (closedBall 0 R)) :
    Real.pi * R ^ 2 * ‖F 0‖ ^ 2 ≤ ∫ z in ball (0 : ℂ) R, ‖F z‖ ^ 2 := by
  rw [disk_integral_eq_polar (f := fun z ↦ ‖F z‖ ^ 2) hR (hF.continuousOn.norm.pow 2)]
  exact norm_sq_mul_diskArea_le_polarEnergy hR hF

theorem ofReal_norm_sq_mul_diskArea_le_lintegral {F : ℂ → E} {R : ℝ}
    (hR : 0 ≤ R) (hF : DifferentiableOn ℂ F (closedBall 0 R)) :
    ENNReal.ofReal (Real.pi * R ^ 2 * ‖F 0‖ ^ 2) ≤
      ∫⁻ z in ball (0 : ℂ) R, ENNReal.ofReal (‖F z‖ ^ 2) := by
  have hi : IntegrableOn (fun z ↦ ‖F z‖ ^ 2) (ball (0 : ℂ) R) :=
    ((hF.continuousOn.norm.pow 2).integrableOn_compact
      (isCompact_closedBall 0 R)).mono_set ball_subset_closedBall
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (norm_sq_mul_diskArea_le_integral hR hF)

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ} {X : ComplexManifold n}

theorem curveArea_mono (g : KahlerMetric X) (f : ℂ → X.Carrier)
    {U V : Set ℂ} (h : U ⊆ V) : curveArea g f U ≤ curveArea g f V :=
  lintegral_mono_set h

theorem curveArea_eq_ofReal_integral (g : KahlerMetric X) (f : ℂ → X.Carrier)
    {U : Set ℂ} (hi : IntegrableOn (fun z ↦ curveSpeed g f z ^ 2) U) :
    curveArea g f U = ENNReal.ofReal (∫ z in U, curveSpeed g f z ^ 2) :=
  (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))).symm

theorem exists_normalized_curveArea_lowerBound (g : KahlerMetric X)
    (c : X.Carrier) {δ : ℝ} (hδ : 0 < δ) :
    ∃ V ∈ 𝓝 c, ∃ κ : ℝ, 0 < κ ∧ ∀ h : ℂ → X.Carrier,
      MDifferentiableOn 𝓘(ℂ, ℂ) (model n) h (ball 0 δ) →
      h 0 ∈ V → curveSpeed g h 0 = 1 →
      (∀ z ∈ ball 0 δ, curveSpeed g h z ≤ 2) →
      ENNReal.ofReal κ ≤ curveArea g h (ball 0 δ) := by
  let e : OpenPartialHomeomorph X.Carrier (Model n) :=
    { extChartAt (model n) c with
      continuousOn_toFun := continuousOn_extChartAt c
      continuousOn_invFun := continuousOn_extChartAt_symm c
      open_source := isOpen_extChartAt_source c
      open_target := isOpen_extChartAt_target c }
  have hc : c ∈ e.source := mem_extChartAt_source c
  obtain ⟨R,hR,he⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (e.open_target.mem_nhds (e.map_source hc))
  obtain ⟨Cforward,Cback,hC,hD,hcomp⟩ := g.exists_chart_speed_comparison c (isCompact_closedBall (e c) R) he
  let V := e.source ∩ e ⁻¹' ball (e c) (R/2)
  have hV : V ∈ 𝓝 c := (e.isOpen_inter_preimage isOpen_ball).mem_nhds
    ⟨hc, by simpa using half_pos hR⟩
  let r := min (δ/2) (R/(8*Cforward))
  have hr : 0 < r := lt_min (half_pos hδ) (div_pos hR (by positivity))
  have hrδ : r < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hrC : 2*Cforward*r ≤ R/4 := by
    have hm := mul_le_mul_of_nonneg_left (min_le_right (δ/2) (R/(8*Cforward))) (show 0 ≤ 2*Cforward by positivity)
    dsimp [r]
    calc
      2*Cforward*min (δ/2) (R/(8*Cforward)) ≤ 2*Cforward*(R/(8*Cforward)) := hm
      _ = R/4 := by field_simp; ring
  let κ := Real.pi * r^2 / (Cforward^2 * Cback ^ 2)
  refine ⟨V,hV,κ,by dsimp [κ]; positivity,?_⟩
  intro h hh hhV hnorm hbound
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 δ := closedBall_subset_ball hrδ
  have hhcont := hh.continuousOn
  have hderchart (z : ℂ) (hz : z ∈ ball 0 δ) (hs : h z ∈ e.source) :
      DifferentiableAt ℂ (e ∘ h) z := by
    have he' : MDifferentiableAt (model n) (model n) e (h z) :=
      mdifferentiableAt_extChartAt (by simpa only [e,extChartAt_source] using hs)
    exact (he'.comp z (hh.mdifferentiableAt (isOpen_ball.mem_nhds hz))).differentiableAt
  have htrap : ∀ z ∈ closedBall (0 : ℂ) r, h z ∈ e.source ∧ e (h z) ∈ ball (e c) R := by
    apply chart_trapping_on_disk e hR (by positivity : 0 ≤ 2*Cforward) hr.le he (hhcont.mono hsub)
    · refine ⟨hhV.1,?_⟩
      have hi : dist (e (h 0)) (e c) < R/2 := hhV.2
      linarith
    · intro z hz hk
      obtain ⟨w,hw,hwz⟩ := hk
      have hs : h z ∈ e.source := hwz ▸ e.map_target (he hw)
      have hw' : e (h z) ∈ closedBall (e c) R := by rw [← hwz,e.right_inv (he hw)]; exact hw
      refine ⟨hderchart z (hsub hz) hs,?_⟩
      rw [← norm_deriv_eq_norm_fderiv]
      change ‖deriv ((extChartAt (model n) c) ∘ h) z‖ ≤ _
      rw [chart_deriv_curve (hh.mdifferentiableAt (isOpen_ball.mem_nhds (hsub hz))) c hs]
      exact ((hcomp (h z) hs hw' (mfderiv 𝓘(ℂ, ℂ) (model n) h z (1 : ℂ))).1).trans
        (by change Cforward * curveSpeed g h z ≤ 2*Cforward; nlinarith [hbound z (hsub hz)])
  let W := ball (0 : ℂ) δ ∩ h ⁻¹' e.source
  have hW : IsOpen W := hhcont.isOpen_inter_preimage isOpen_ball e.open_source
  have hd : DifferentiableOn ℂ (e ∘ h) W :=
    fun z hz ↦ (hderchart z hz.1 hz.2).differentiableWithinAt
  have hrW : closedBall (0 : ℂ) r ⊆ W := fun z hz ↦ ⟨hsub hz,(htrap z hz).1⟩
  have hDhol : DifferentiableOn ℂ (deriv (e ∘ h)) (closedBall 0 r) := (hd.deriv hW).mono hrW
  have hDs (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) :
      ‖deriv (e ∘ h) z‖ ≤ Cforward * curveSpeed g h z ∧
      curveSpeed g h z ≤ Cback * ‖deriv (e ∘ h) z‖ := by
    change ‖deriv ((extChartAt (model n) c) ∘ h) z‖ ≤ _ ∧
      _ ≤ Cback * ‖deriv ((extChartAt (model n) c) ∘ h) z‖
    rw [chart_deriv_curve (hh.mdifferentiableAt (isOpen_ball.mem_nhds (hsub hz))) c (htrap z hz).1]
    exact hcomp (h z) (htrap z hz).1 (ball_subset_closedBall (htrap z hz).2)
      (mfderiv 𝓘(ℂ, ℂ) (model n) h z (1 : ℂ))
  have hzero : (0 : ℂ) ∈ closedBall 0 r := mem_closedBall_self hr.le
  have hone : 1 ≤ Cback ^ 2 * ‖deriv (e ∘ h) 0‖^2 := by
    have h1 : 1 ≤ Cback * ‖deriv (e ∘ h) 0‖ := by simpa only [hnorm] using (hDs 0 hzero).2
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h1 2
    simpa only [one_pow,mul_pow] using hsq
  have hspeedcont := (curveSpeed_continuousOn g isOpen_ball hh).mono hsub
  have hi : IntegrableOn (fun z ↦ curveSpeed g h z ^ 2) (ball (0 : ℂ) r) :=
    ((hspeedcont.pow 2).integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hDi : IntegrableOn (fun z ↦ ‖deriv (e ∘ h) z‖^2) (ball (0 : ℂ) r) :=
    ((hDhol.continuousOn.norm.pow 2).integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hupper : (∫ z in ball (0 : ℂ) r, ‖deriv (e ∘ h) z‖^2) ≤
      Cforward^2 * ∫ z in ball (0 : ℂ) r, curveSpeed g h z ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hDi (hi.const_mul _) measurableSet_ball
    intro z hz
    have hs := pow_le_pow_left₀ (norm_nonneg _) (hDs z (ball_subset_closedBall hz)).1 2
    simpa only [mul_pow] using hs
  have hlower := (norm_sq_mul_diskArea_le_integral hr.le hDhol).trans hupper
  have hκ : κ ≤ ∫ z in ball (0 : ℂ) r, curveSpeed g h z ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < Cforward^2*Cback ^ 2)).mpr
    calc
      Real.pi*r^2 ≤ (Real.pi*r^2*‖deriv (e ∘ h) 0‖^2)*Cback ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hone (show 0 ≤ Real.pi*r^2 by positivity)]
      _ ≤ (Cforward^2 * ∫ z in ball (0 : ℂ) r, curveSpeed g h z ^ 2)*Cback ^ 2 :=
        mul_le_mul_of_nonneg_right hlower (sq_nonneg Cback)
      _ = (∫ z in ball (0 : ℂ) r, curveSpeed g h z ^ 2)*(Cforward^2*Cback ^ 2) := by ring
  exact ((ENNReal.ofReal_le_ofReal hκ).trans_eq (curveArea_eq_ofReal_integral g h hi).symm).trans
    (curveArea_mono g h (ball_subset_ball hrδ.le))

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ} {X : ComplexManifold n}

theorem exists_uniform_normalized_curveArea_lowerBound [CompactSpace X.Carrier]
    (g : KahlerMetric X) {δ : ℝ} (hδ : 0 < δ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ h : ℂ → X.Carrier,
      MDifferentiableOn 𝓘(ℂ, ℂ) (model n) h (ball 0 δ) →
      curveSpeed g h 0 = 1 →
      (∀ z ∈ ball 0 δ, curveSpeed g h z ≤ 2) →
      ENNReal.ofReal κ ≤ curveArea g h (ball 0 δ) := by
  classical
  choose V hV κ hκ hb using fun c : X.Carrier ↦
    exists_normalized_curveArea_lowerBound g c hδ
  obtain ⟨s,hs⟩ := CompactSpace.elim_nhds_subcover V hV
  have covered (x : X.Carrier) : ∃ c ∈ s, x ∈ V c := by
    have hx : x ∈ ⋃ c ∈ s, V c := by rw [hs]; trivial
    simpa only [mem_iUnion,exists_prop] using hx
  by_cases hne : s.Nonempty
  · refine ⟨s.inf' hne κ, (Finset.lt_inf'_iff hne).mpr (fun c _ ↦ hκ c),?_⟩
    intro h hh hnorm hbound
    obtain ⟨c,hcs,hc⟩ := covered (h 0)
    exact (ENNReal.ofReal_le_ofReal (s.inf'_le κ hcs)).trans (hb c h hh hc hnorm hbound)
  · refine ⟨1,by norm_num,?_⟩
    intro h
    obtain ⟨c,hcs,_⟩ := covered (h 0)
    exact (hne ⟨c,hcs⟩).elim

end UniversalCoverSplitting

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace UniversalCoverSplitting

theorem lintegral_comp_positive_affine (F : ℂ → ℝ≥0∞) (U : Set ℂ)
    (p : ℂ) {a : ℝ} (ha : 0 < a) :
    (∫⁻ z in U, F (p + a • z)) = (ENNReal.ofReal (a^2))⁻¹ *
      ∫⁻ w in (fun z : ℂ ↦ p + a • z) '' U, F w := by
  let e : ℂ ≃ₜ ℂ := (Homeomorph.smulOfNeZero a ha.ne').trans (Homeomorph.addLeft p)
  have hm : Measure.map e (volume : Measure ℂ) = (ENNReal.ofReal (a^2))⁻¹ • volume := by
    change Measure.map ((fun z : ℂ ↦ p + z) ∘ (fun z : ℂ ↦ a • z)) volume = _
    rw [← Measure.map_map (measurable_const_add p) (measurable_const_smul a),
      Measure.map_addHaar_smul volume ha.ne',
      Measure.map_smul _ (measurable_const_add p).aemeasurable,
      map_add_left_eq_self,Complex.finrank_real_complex,abs_of_pos (by positivity : 0 < (a^2)⁻¹),
      ENNReal.ofReal_inv_of_pos (by positivity)]
  have hr := e.toMeasurableEquiv.restrict_map (volume : Measure ℂ) (e '' U)
  change (Measure.map e volume).restrict (e '' U) =
    Measure.map e (volume.restrict (e ⁻¹' (e '' U))) at hr
  rw [e.injective.preimage_image] at hr
  calc
    (∫⁻ z in U, F (p + a • z)) = ∫⁻ z, F z ∂Measure.map e (volume.restrict U) :=
      (lintegral_map_equiv F e.toMeasurableEquiv).symm
    _ = ∫⁻ z in e '' U, F z ∂Measure.map e volume := by rw [← hr]
    _ = (ENNReal.ofReal (a^2))⁻¹ * ∫⁻ z in e '' U, F z := by
      rw [hm,Measure.restrict_smul,lintegral_smul_measure,smul_eq_mul]
    _ = _ := rfl

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set Metric MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ} {X : ComplexManifold n}

theorem curveArea_positive_affine (g : KahlerMetric X) {f : ℂ → X.Carrier}
    (U : Set ℂ) (hU : MeasurableSet U) (p : ℂ) {a : ℝ} (ha : 0 < a)
    (hf : ∀ z ∈ (fun z : ℂ ↦ p + a • z) '' U,
      MDifferentiableAt 𝓘(ℂ, ℂ) (model n) f z) :
    curveArea g (fun z ↦ f (p + a • z)) U =
      curveArea g f ((fun z : ℂ ↦ p + a • z) '' U) := by
  have hs (z : ℂ) (hz : z ∈ U) :
      curveSpeed g (fun z ↦ f (p + a • z)) z = a * curveSpeed g f (p + a • z) := by
    simpa only [Complex.real_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] using
      curveSpeed_affine g p (a : ℂ) z (hf _ ⟨z,hz,rfl⟩)
  unfold curveArea
  calc
    (∫⁻ z in U, ENNReal.ofReal (curveSpeed g (fun z ↦ f (p + a • z)) z ^ 2)) =
        ∫⁻ z in U, ENNReal.ofReal (a^2) * ENNReal.ofReal (curveSpeed g f (p + a • z) ^ 2) := by
      apply setLIntegral_congr_fun hU
      intro z hz
      dsimp only
      rw [hs z hz,mul_pow,ENNReal.ofReal_mul (sq_nonneg a)]
    _ = ENNReal.ofReal (a^2) * ∫⁻ z in U, ENNReal.ofReal (curveSpeed g f (p + a • z) ^ 2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (a^2) * ((ENNReal.ofReal (a^2))⁻¹ *
        ∫⁻ w in (fun z : ℂ ↦ p + a • z) '' U, ENNReal.ofReal (curveSpeed g f w ^ 2)) := by
      rw [lintegral_comp_positive_affine (fun w ↦ ENNReal.ofReal (curveSpeed g f w ^ 2)) U p ha]
    _ = _ := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top,one_mul]

end UniversalCoverSplitting
end
end
end
end
end
end
end
end

end OAI
