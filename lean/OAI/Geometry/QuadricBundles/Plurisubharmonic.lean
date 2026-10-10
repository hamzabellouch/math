import OAI.Geometry.QuadricBundles.DiskHessian

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory
noncomputable section
open scoped Pointwise
def radialIntegral (u : ℂ → ℝ) (c z : ℂ) : ℝ :=
  ∫ a in closedBall (0 : ℂ) 1, u (c + a*z)

lemma radialIntegral_zero (u : ℂ → ℝ) (c : ℂ) :
    radialIntegral u c 0 = (volume (closedBall (0 : ℂ) 1)).toReal * u c := by
  simp [radialIntegral,measureReal_def]

lemma radialIntegral_rotation (u : ℂ → ℝ) (c z : ℂ) (η : Circle) :
    radialIntegral u c ((η : ℂ)*z) = radialIntegral u c z := by
  have he : (rotation η) ⁻¹' closedBall (0 : ℂ) 1 = closedBall 0 1 := by
    ext a
    simp only [mem_preimage,mem_closedBall,dist_zero_right,rotation_apply,
      norm_mul,Circle.norm_coe,one_mul]
  have hp := (rotation η).measurePreserving.restrict_preimage (s := closedBall (0 : ℂ) 1) measurableSet_closedBall
  rw [he] at hp
  have hi := hp.integral_comp (rotation η).toHomeomorph.measurableEmbedding
    (fun a : ℂ ↦ u (c+a*z))
  simpa only [radialIntegral,rotation_apply,mul_assoc,mul_left_comm] using hi

lemma radialIntegral_eq_of_norm_eq (u : ℂ → ℝ) (c : ℂ) {z w : ℂ}
    (h : ‖z‖ = ‖w‖) : radialIntegral u c z = radialIntegral u c w := by
  by_cases hw : w=0
  · have hz : z=0 := norm_eq_zero.mp (by simpa [hw] using h)
    simp [hw,hz]
  · let η : Circle := ⟨z/w,by change z/w ∈ sphere (0 : ℂ) 1; rw [mem_sphere_zero_iff_norm]; simp [h,norm_ne_zero_iff.mpr hw]⟩
    have he : (η : ℂ)*w=z := by simp [η,div_mul_cancel₀ _ hw]
    rw [← he]
    exact radialIntegral_rotation u c w η

lemma radialIntegral_pos_radius (u : ℂ → ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    radialIntegral u c (R : ℂ) = (R^2)⁻¹ * ∫ y in closedBall c R, u y := by
  have hs : R • closedBall (0 : ℂ) 1 = closedBall 0 R := by
    simpa [abs_of_nonneg hR.le] using smul_closedBall' hR.ne' (0 : ℂ) 1
  have hi := Measure.setIntegral_comp_smul_of_pos volume
    (fun y : ℂ ↦ u (c+y)) (closedBall 0 1) hR
  rw [hs] at hi
  have ht := (measurePreserving_add_left volume c).setIntegral_image_emb
    (Homeomorph.addLeft c).measurableEmbedding u (closedBall (0 : ℂ) R)
  have he : (fun y : ℂ ↦ c+y) '' closedBall 0 R = closedBall c R := by
    ext y
    constructor
    · rintro ⟨a,ha,rfl⟩
      simpa only [mem_closedBall,dist_zero_right,dist_self_add_left] using ha
    · intro hy
      refine ⟨y-c,?_,by ring⟩
      simpa only [mem_closedBall,dist_zero_right,dist_eq_norm,sub_zero] using hy
  rw [he] at ht
  simp only [Complex.finrank_real_complex,smul_eq_mul] at hi
  simpa only [radialIntegral,Complex.real_smul,mul_comm] using
    hi.trans (congrArg (fun t : ℝ ↦ (R^2)⁻¹*t) ht.symm)

attribute [local instance] Measure.Subtype.measureSpace

lemma complex_closedBall_ae_ball (c : ℂ) (r : ℝ) :
    closedBall c r =ᵐ[volume] ball c r := by
  have h := measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume c r)
  filter_upwards [h] with x hx
  apply propext
  exact ⟨fun hh ↦ lt_of_le_of_ne hh (by simpa only [mem_sphere] using hx),
    fun hx ↦ mem_closedBall.mpr (mem_ball.mp hx).le⟩

lemma compact_integral_continuousOn
    {α : Type u1} [TopologicalSpace α] [CompactSpace α] [T2Space α]
    [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
    {μ : Measure α} [IsFiniteMeasure μ] {c : ℂ} {r : ℝ}
    {F : α → ℂ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ closedBall c r)) :
    ContinuousOn (fun z ↦ ∫ a, F a z ∂μ) (closedBall c r) := by
  have hc : Continuous (fun p : (closedBall c r) × α ↦ F p.2 p.1) :=
    hF.comp_continuous (f := fun p : (closedBall c r) × α ↦ (p.2,(p.1 : ℂ)))
      (by fun_prop) (fun p ↦ ⟨mem_univ _,p.1.property⟩)
  have hi := continuous_parametric_integral_of_continuous (μ := μ)
    (f := fun z : closedBall c r ↦ fun a : α ↦ F a z) hc isCompact_univ
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert hi using 1
  ext z
  simp only [setIntegral_univ,Set.domRestrict_apply]

def radialLinear (a : ℂ) : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ a
@[simp] lemma radialLinear_apply (a z : ℂ) : radialLinear a z=a*z := rfl

def radialFirst (u : ℂ → ℝ) (c : ℂ) (a z : ℂ) : ℂ →L[ℝ] ℝ :=
  (fderiv ℝ u (c+a*z)).comp (radialLinear a)
def radialSecond (u : ℂ → ℝ) (c : ℂ) (a z : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip (radialLinear a)).comp
    ((fderiv ℝ (fderiv ℝ u) (c+a*z)).comp (radialLinear a))

@[simp] lemma radialSecond_apply (u : ℂ → ℝ) (c a z v w : ℂ) :
    radialSecond u c a z v w =
      (fderiv ℝ (fderiv ℝ u) (c+a*z) (a*v)) (a*w) := rfl

lemma radialFirst_hasFDerivAt {u : ℂ → ℝ} {c a z : ℂ}
    (hu : DifferentiableAt ℝ u (c+a*z)) :
    HasFDerivAt (fun x : ℂ ↦ u (c+a*x)) (radialFirst u c a z) z := by
  exact hu.hasFDerivAt.comp z ((radialLinear a).hasFDerivAt.const_add c)

lemma radialSecond_hasFDerivAt {u : ℂ → ℝ} {c a z : ℂ}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) (c+a*z)) :
    HasFDerivAt (radialFirst u c a) (radialSecond u c a z) z := by
  exact ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip (radialLinear a)).hasFDerivAt.comp z
    (hu.hasFDerivAt.comp z ((radialLinear a).hasFDerivAt.const_add c))

lemma radialFamily_maps_closedBall {c : ℂ} {R : ℝ} (_hR : 0 ≤ R)
    (a : closedBall (0 : ℂ) 1) (z : ℂ) (hz : z∈closedBall 0 R) :
    c+(a : ℂ)*z ∈ closedBall c R := by
  rw [mem_closedBall,dist_self_add_left,norm_mul]
  have ha : ‖(a : ℂ)‖≤1 := by simpa only [mem_closedBall,dist_zero_right] using a.property
  have hz' : ‖z‖≤R := by simpa only [mem_closedBall,dist_zero_right] using hz
  nlinarith [mul_le_mul ha hz' (norm_nonneg z) (by norm_num : (0 : ℝ)≤1)]

lemma radialFamily_continuous {u : ℂ → ℝ} {D : Set ℂ} {c : ℂ} {R : ℝ}
    (hR : 0≤R) (hu : ContinuousOn u D) (hb : closedBall c R⊆D) :
    ContinuousOn (fun p : closedBall (0 : ℂ) 1 × ℂ ↦ u (c+(p.1 : ℂ)*p.2))
      (univ ×ˢ closedBall 0 R) := by
  exact hu.comp (by fun_prop) (fun p hp ↦ hb (radialFamily_maps_closedBall hR p.1 p.2 hp.2))

lemma radialFirst_continuous {u : ℂ → ℝ} {D : Set ℂ} {c : ℂ} {R : ℝ}
    (hD : IsOpen D) (hR : 0≤R) (hu : ContDiffOn ℝ 2 u D) (hb : closedBall c R⊆D) :
    ContinuousOn (fun p : closedBall (0 : ℂ) 1 × ℂ ↦ radialFirst u c p.1 p.2)
      (univ ×ˢ closedBall 0 R) := by
  have hfd : ContinuousOn (fderiv ℝ u) D :=
    (hu.fderiv_of_isOpen hD (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).continuousOn
  have hf := hfd.comp (show ContinuousOn (fun p : closedBall (0 : ℂ) 1 × ℂ ↦
    c+(p.1 : ℂ)*p.2) (univ ×ˢ closedBall 0 R) by fun_prop)
    (fun p hp ↦ hb (radialFamily_maps_closedBall hR p.1 p.2 hp.2))
  exact hf.clm_comp (show ContinuousOn (fun p : closedBall (0 : ℂ) 1 × ℂ ↦ radialLinear p.1)
    (univ ×ˢ closedBall 0 R) from (ContinuousLinearMap.mul ℝ ℂ).continuous.continuousOn.comp
      (by fun_prop) (mapsTo_univ _ _))

lemma radialSecond_continuous {u : ℂ → ℝ} {D : Set ℂ} {c : ℂ} {R : ℝ}
    (hD : IsOpen D) (hR : 0≤R) (hu : ContDiffOn ℝ 2 u D) (hb : closedBall c R⊆D) :
    ContinuousOn (fun p : closedBall (0 : ℂ) 1 × ℂ ↦ radialSecond u c p.1 p.2)
      (univ ×ˢ closedBall 0 R) := by
  have hfd : ContinuousOn (fderiv ℝ (fderiv ℝ u)) D :=
    ((hu.fderiv_of_isOpen hD (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).fderiv_of_isOpen
      hD (by norm_num : 0+1 ≤ (1 : WithTop ℕ∞))).continuousOn
  have hf := hfd.comp (show ContinuousOn (fun p : closedBall (0 : ℂ) 1 × ℂ ↦
    c+(p.1 : ℂ)*p.2) (univ ×ˢ closedBall 0 R) by fun_prop)
    (fun p hp ↦ hb (radialFamily_maps_closedBall hR p.1 p.2 hp.2))
  have hL : ContinuousOn (fun p : closedBall (0 : ℂ) 1 × ℂ ↦ radialLinear p.1)
      (univ ×ˢ closedBall 0 R) :=
    (ContinuousLinearMap.mul ℝ ℂ).continuous.continuousOn.comp (by fun_prop) (mapsTo_univ _ _)
  exact (((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip).continuous.comp_continuousOn hL).clm_comp
    (hf.clm_comp hL)

lemma radialIntegral_C2 {u : ℂ → ℝ} {D : Set ℂ} {c : ℂ} {R : ℝ}
    (hD : IsOpen D) (hR : 0<R) (hu : ContDiffOn ℝ 2 u D) (hb : closedBall c R⊆D) :
    ContDiffOn ℝ 2 (radialIntegral u c) (ball 0 R) := by
  let A := closedBall (0 : ℂ) 1
  let : IsFiniteMeasure (volume : Measure A) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
    exact (isCompact_closedBall (0 : ℂ) 1).measure_lt_top⟩
  have hd (a : A) (z : ℂ) (hz : z∈ball 0 R) :
      HasFDerivAt (fun x ↦ u (c+(a : ℂ)*x)) (radialFirst u c a z) z := by
    have hx := hb (radialFamily_maps_closedBall hR.le a z (ball_subset_closedBall hz))
    exact radialFirst_hasFDerivAt ((hu (c+(a : ℂ)*z) hx).contDiffAt
      (hD.mem_nhds hx) |>.differentiableAt (by norm_num))
  have hd' (a : A) (z : ℂ) (hz : z∈ball 0 R) :
      HasFDerivAt (radialFirst u c a) (radialSecond u c a z) z := by
    have hx := hb (radialFamily_maps_closedBall hR.le a z (ball_subset_closedBall hz))
    exact radialSecond_hasFDerivAt
      (((hu.fderiv_of_isOpen hD (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))) _ hx).contDiffAt
        (hD.mem_nhds hx) |>.differentiableAt (by norm_num))
  have hh := compactParameter_contDiffOn_two_Integral (μ := (volume : Measure A)) isOpen_ball
    ((radialFamily_continuous hR.le hu.continuousOn hb).mono (prod_mono (Subset.refl univ) ball_subset_closedBall))
    ((radialFirst_continuous hD hR.le hu hb).mono (prod_mono (Subset.refl univ) ball_subset_closedBall))
    ((radialSecond_continuous hD hR.le hu hb).mono (prod_mono (Subset.refl univ) ball_subset_closedBall)) hd hd'
  convert hh using 1
  ext z
  exact (integral_subtype (s := closedBall (0 : ℂ) 1) measurableSet_closedBall
    (fun a : ℂ ↦ u (c+a*z))).symm

local instance realDualComplexGroup : NormedAddCommGroup (ℂ →L[ℝ] ℝ) := inferInstance
local instance realDualComplexSpace : NormedSpace ℝ (ℂ →L[ℝ] ℝ) := inferInstance

lemma integral_bilinear_apply {α : Type u2} [MeasurableSpace α] {μ : Measure α}
    {F : α → ℂ →L[ℝ] ℂ →L[ℝ] ℝ} (hF : Integrable F μ) (v w : ℂ) :
    (∫ a, F a ∂μ) v w = ∫ a, F a v w ∂μ := by
  let ev : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] ℝ) v
  have hv : Integrable (fun a ↦ F a v) μ := ev.integrable_comp hF
  rw [ContinuousLinearMap.integral_apply hF v,ContinuousLinearMap.integral_apply hv w]

lemma radialIntegral_laplacian {u : ℂ → ℝ} {D : Set ℂ} {c : ℂ} {R : ℝ}
    (hD : IsOpen D) (hR : 0<R) (hu : ContDiffOn ℝ 2 u D) (hb : closedBall c R⊆D)
    {z : ℂ} (hz : z∈ball 0 R) :
    complexLaplacian (radialIntegral u c) z =
      ∫ a in closedBall (0 : ℂ) 1, Complex.normSq a*complexLaplacian u (c+a*z) := by
  let A := closedBall (0 : ℂ) 1
  let : IsFiniteMeasure (volume : Measure A) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
    exact (isCompact_closedBall (0 : ℂ) 1).measure_lt_top⟩
  have hd (a : A) (z : ℂ) (hz : z∈ball 0 R) :
      HasFDerivAt (fun x ↦ u (c+(a : ℂ)*x)) (radialFirst u c a z) z := by
    have hx := hb (radialFamily_maps_closedBall hR.le a z (ball_subset_closedBall hz))
    exact radialFirst_hasFDerivAt ((hu (c+(a : ℂ)*z) hx).contDiffAt
      (hD.mem_nhds hx) |>.differentiableAt (by norm_num))
  have hd' (a : A) (z : ℂ) (hz : z∈ball 0 R) :
      HasFDerivAt (radialFirst u c a) (radialSecond u c a z) z := by
    have hx := hb (radialFamily_maps_closedBall hR.le a z (ball_subset_closedBall hz))
    exact radialSecond_hasFDerivAt
      (((hu.fderiv_of_isOpen hD (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))) _ hx).contDiffAt
        (hD.mem_nhds hx) |>.differentiableAt (by norm_num))
  have hF := (radialFamily_continuous hR.le hu.continuousOn hb).mono
    (prod_mono (Subset.refl univ) ball_subset_closedBall)
  have hF' := (radialFirst_continuous hD hR.le hu hb).mono
    (prod_mono (Subset.refl univ) ball_subset_closedBall)
  have hF'' := (radialSecond_continuous hD hR.le hu hb).mono
    (prod_mono (Subset.refl univ) ball_subset_closedBall)
  have hh := compactParameter_secondFDerivIntegral (μ := (volume : Measure A)) isOpen_ball
    hF hF' hF'' hd hd' hz
  have he : (fun z ↦ ∫ a : A, u (c+(a : ℂ)*z))=radialIntegral u c := by
    ext x
    exact integral_subtype (s := closedBall (0 : ℂ) 1) measurableSet_closedBall
      (fun a : ℂ ↦ u (c+a*x))
  rw [he] at hh
  have hH : Integrable (fun a : A ↦ radialSecond u c a z) :=
    compactParameter_integrable (F := fun a : A ↦ radialSecond u c a) hz hF''
  have hHv (v w : ℂ) : Integrable (fun a : A ↦ radialSecond u c a z v w) := by
    let ev : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
      ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] ℝ) v
    have hv : Integrable (fun a : A ↦ radialSecond u c a z v) := ev.integrable_comp hH
    exact (ContinuousLinearMap.apply ℝ ℝ w).integrable_comp hv
  unfold complexLaplacian
  rw [hh,integral_bilinear_apply hH 1 1,integral_bilinear_apply hH Complex.I Complex.I,
    ← integral_add (hHv 1 1) (hHv Complex.I Complex.I)]
  rw [← integral_subtype (s := closedBall (0 : ℂ) 1) measurableSet_closedBall]
  apply integral_congr_ae
  exact Eventually.of_forall fun a ↦ by
    simpa only [radialSecond_apply,mul_one,mul_comm (a : ℂ) Complex.I] using
      rotated_hessian_trace (fderiv ℝ (fderiv ℝ u) (c+(a : ℂ)*z)) a

lemma radialIntegral_laplacian_nonneg {u : ℂ → ℝ} {D : Set ℂ} {c : ℂ} {R : ℝ}
    (hD : IsOpen D) (hR : 0<R) (hu : ContDiffOn ℝ 2 u D) (hb : closedBall c R⊆D)
    (hΔ : ∀ z∈D, 0≤complexLaplacian u z) {z : ℂ} (hz : z∈ball 0 R) :
    0≤complexLaplacian (radialIntegral u c) z := by
  rw [radialIntegral_laplacian hD hR hu hb hz]
  apply setIntegral_nonneg measurableSet_closedBall
  intro a ha
  exact mul_nonneg (Complex.normSq_nonneg a)
    (hΔ _ (hb (radialFamily_maps_closedBall hR.le ⟨a,ha⟩ z (ball_subset_closedBall hz))))

theorem C2_disk_submean {u : ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D)
    (hu : ContDiffOn ℝ 2 u D) (hΔ : ∀ z∈D, 0≤complexLaplacian u z)
    {c : ℂ} {R : ℝ} (hR : 0<R) (hb : closedBall c R⊆D) :
    (volume (ball c R)).toReal*u c ≤ ∫ y in ball c R, u y := by
  let A := closedBall (0 : ℂ) 1
  let : IsFiniteMeasure (volume : Measure A) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
    exact (isCompact_closedBall (0 : ℂ) 1).measure_lt_top⟩
  have he : (fun z ↦ ∫ a : A, u (c+(a : ℂ)*z))=radialIntegral u c := by
    ext x
    exact integral_subtype (s := closedBall (0 : ℂ) 1) measurableSet_closedBall
      (fun a : ℂ ↦ u (c+a*x))
  have hc : ContinuousOn (radialIntegral u c) (closedBall 0 R) := by
    rw [← he]
    exact compact_integral_continuousOn (radialFamily_continuous hR.le hu.continuousOn hb)
  have hm0 := C2_le_boundary hR hc (radialIntegral_C2 hD hR hu hb)
    (fun z hz ↦ radialIntegral_laplacian_nonneg hD hR hu hb hΔ hz)
    (M := radialIntegral u c (R : ℂ)) (by
      intro z hz
      apply le_of_eq
      apply radialIntegral_eq_of_norm_eq
      simpa only [mem_sphere,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR] using hz)
    0 (mem_closedBall_self hR.le)
  rw [radialIntegral_zero,radialIntegral_pos_radius _ _ hR] at hm0
  have hv := radialIntegral_pos_radius (fun _ ↦ (1 : ℝ)) c hR
  simp only [radialIntegral,setIntegral_const,measureReal_def,smul_eq_mul,mul_one] at hv
  have heR := complex_closedBall_ae_ball c R
  rw [measure_congr heR] at hv
  rw [← setIntegral_congr_set heR]
  have hn : R^2 ≠ 0 := pow_ne_zero _ hR.ne'
  have hscale : R^2 * (R^2)⁻¹ = 1 := mul_inv_cancel₀ hn
  have hmul := mul_le_mul_of_nonneg_left hm0 (sq_nonneg R)
  calc
    (volume (ball c R)).toReal * u c =
        R^2 * ((volume (closedBall (0 : ℂ) 1)).toReal * u c) := by
      rw [hv]
      rw [← mul_assoc,← mul_assoc,hscale,one_mul]
    _ ≤ R^2 * ((R^2)⁻¹ * ∫ y in closedBall c R, u y) := hmul
    _ = ∫ y in closedBall c R, u y := by rw [← mul_assoc,hscale,one_mul]

def DiskSubharmonicOn (Ω : Set ℂ) (u : ℂ → ℝ) : Prop :=
  UpperSemicontinuousOn u Ω ∧ ∀ x ∈ Ω, ∀ r : ℝ, 0 < r → closedBall x r ⊆ Ω →
    IntegrableOn u (ball x r) ∧
      (volume (ball x r)).toReal * u x ≤ ∫ y in ball x r, u y

theorem DiskSubharmonicOn.of_C2_laplacian_nonneg {u : ℂ → ℝ} {D : Set ℂ}
    (hD : IsOpen D) (hu : ContDiffOn ℝ 2 u D) (hΔ : ∀ z∈D, 0≤complexLaplacian u z) :
    DiskSubharmonicOn D u := by
  refine ⟨hu.continuousOn.upperSemicontinuousOn,fun c _ R hR hb ↦ ⟨?_,C2_disk_submean hD hu hΔ hR hb⟩⟩
  exact ((hu.continuousOn.mono hb).integrableOn_compact (isCompact_closedBall c R)).mono_set ball_subset_closedBall

lemma hessian_comp_apply {X : Type u3} {Y : Type u4} {Z : Type u5}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y} {g : Y → Z} {x : X}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g (f x)) (v w : X) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) x v w =
      fderiv ℝ (fderiv ℝ g) (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) +
        fderiv ℝ g (f x) (fderiv ℝ (fderiv ℝ f) x v w) := by
  have hf1 := hf.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hf2 := (hf.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hg2 := (hg.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have he : fderiv ℝ (g ∘ f) =ᶠ[𝓝 x]
      (fun y ↦ (fderiv ℝ g (f y)).comp (fderiv ℝ f y)) := by
    filter_upwards [hf.eventually (by norm_num),
      hf.continuousAt.eventually (hg.eventually (by norm_num))] with y hy hy'
    exact fderiv_comp y (hy'.differentiableAt (by norm_num))
      (hy.differentiableAt (by norm_num))
  have hc := (hg2.hasFDerivAt.comp x hf1.hasFDerivAt).clm_comp hf2.hasFDerivAt
  dsimp only [Function.comp_def] at hc
  rw [he.fderiv_eq,hc.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply]
  exact add_comm _ _

lemma holomorphic_real_hessian_trace {E : Type u6} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E] {γ : ℂ → E} {z : ℂ} (hγ : AnalyticAt ℂ γ z) :
    fderiv ℝ (fderiv ℝ γ) z 1 1 +
      fderiv ℝ (fderiv ℝ γ) z Complex.I Complex.I = 0 := by
  have hh := hγ.harmonicAt.2.self_of_nhds
  simpa only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.empty_val',Pi.zero_apply] using hh

lemma holomorphic_real_derivative_I {E : Type u7} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    {γ : ℂ → E} {z : ℂ} (hγ : DifferentiableAt ℂ γ z) :
    fderiv ℝ γ z Complex.I = Complex.I • fderiv ℝ γ z 1 := by
  rw [hγ.fderiv_restrictScalars ℝ]
  change fderiv ℂ γ z Complex.I = Complex.I • fderiv ℂ γ z 1
  rw [← map_smul]
  simp

def leviTrace {E : Type u8} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (q : E → ℝ) (x v : E) : ℝ :=
  fderiv ℝ (fderiv ℝ q) x v v +
    fderiv ℝ (fderiv ℝ q) x (Complex.I • v) (Complex.I • v)

lemma holomorphic_disk_hessian_trace {E : Type u9} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E] {γ : ℂ → E} {q : E → ℝ} {z : ℂ}
    (hγ : AnalyticAt ℂ γ z) (hq : ContDiffAt ℝ 2 q (γ z)) :
    fderiv ℝ (fderiv ℝ (q ∘ γ)) z 1 1 +
      fderiv ℝ (fderiv ℝ (q ∘ γ)) z Complex.I Complex.I =
        leviTrace q (γ z) (fderiv ℝ γ z 1) := by
  have hc : ContDiffAt ℝ 2 γ z := hγ.contDiffAt.restrict_scalars ℝ
  rw [hessian_comp_apply hc hq,hessian_comp_apply hc hq]
  rw [holomorphic_real_derivative_I hγ.differentiableAt]
  have hh := holomorphic_real_hessian_trace hγ
  have he := congrArg (fderiv ℝ q (γ z)) hh
  rw [map_add,map_zero] at he
  unfold leviTrace
  linarith

def DiskPshOn {E : Type u10} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Ω : Set E) (q : E → ℝ) : Prop :=
  UpperSemicontinuousOn q Ω ∧ ∀ (D : Set ℂ), IsOpen D → ∀ γ : ℂ → E,
    DifferentiableOn ℂ γ D → MapsTo γ D Ω → DiskSubharmonicOn D (q ∘ γ)

theorem DiskPshOn.of_C2_leviTrace_nonneg {E : Type u11} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {Ω : Set E} {q : E → ℝ}
    (hΩ : IsOpen Ω) (hq : ContDiffOn ℝ 2 q Ω)
    (hlevi : ∀ x∈Ω, ∀ v : E, 0≤leviTrace q x v) : DiskPshOn Ω q := by
  refine ⟨hq.continuousOn.upperSemicontinuousOn, ?_⟩
  intro D hD γ hγ hmap
  have ha : ∀ z∈D, AnalyticAt ℂ γ z := fun z hz ↦
    hγ.analyticOnNhd hD z hz
  apply DiskSubharmonicOn.of_C2_laplacian_nonneg hD
  · intro z hz
    exact ((hq.contDiffAt (hΩ.mem_nhds (hmap hz))).comp z
      ((ha z hz).contDiffAt.restrict_scalars ℝ)).contDiffWithinAt
  · intro z hz
    change 0≤fderiv ℝ (fderiv ℝ (q ∘ γ)) z 1 1 +
      fderiv ℝ (fderiv ℝ (q ∘ γ)) z Complex.I Complex.I
    rw [holomorphic_disk_hessian_trace (ha z hz) (hq.contDiffAt (hΩ.mem_nhds (hmap hz)))]
    exact hlevi (γ z) (hmap hz) _

end
end QuadricCounterexample

end OAI
