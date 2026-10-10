import Mathlib
import OAI.Geometry.BallPacking.Surfaces.QuadricInfinityDiffeomorph

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology ENNReal
open Set Function MeasureTheory
open Filter
open scoped Manifold

def areaPolarRadial (p : Plane) : Plane :=
  (Real.sqrt (p.1/Real.pi),2*Real.pi*(p.2-1/2))

def areaPolar (p : Plane) : Plane := polarCoord.symm (areaPolarRadial p)

def areaPolarDomain : Set Plane := Ioi 0 ×ˢ Ioo 0 1

theorem areaPolarRadial_smoothAt {p : Plane} (hp : 0 < p.1) :
    ContDiffAt ℝ ∞ areaPolarRadial p := by
  exact ((contDiffAt_fst.div_const Real.pi).sqrt (div_pos hp Real.pi_pos).ne').prodMk
    (contDiffAt_const.mul (contDiffAt_snd.sub contDiffAt_const))

theorem areaPolar_smoothAt {p : Plane} (hp : 0 < p.1) :
    ContDiffAt ℝ ∞ areaPolar p :=
  polar_smooth.contDiffAt.comp p (areaPolarRadial_smoothAt hp)

theorem areaPolarRadial_target {p : Plane} (hp : p ∈ areaPolarDomain) :
    areaPolarRadial p ∈ polarCoord.target := by
  change 0 < Real.sqrt (p.1/Real.pi) ∧
    -Real.pi < 2*Real.pi*(p.2-1/2) ∧ 2*Real.pi*(p.2-1/2) < Real.pi
  refine ⟨Real.sqrt_pos.mpr (div_pos hp.1 Real.pi_pos),?_,?_⟩
  · nlinarith [mul_pos Real.pi_pos hp.2.1]
  · nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hp.2.2)]

theorem areaPolar_injOn : InjOn areaPolar areaPolarDomain := by
  intro p hp q hq he
  have he' := polarCoord.symm.injOn (areaPolarRadial_target hp) (areaPolarRadial_target hq) he
  have ha := congrArg (fun x : Plane => x.1^2) he'
  have hb := congrArg Prod.snd he'
  change (Real.sqrt (p.1/Real.pi))^2 = (Real.sqrt (q.1/Real.pi))^2 at ha
  rw [Real.sq_sqrt (div_nonneg hp.1.le Real.pi_pos.le),
    Real.sq_sqrt (div_nonneg hq.1.le Real.pi_pos.le)] at ha
  change 2*Real.pi*(p.2-1/2) = 2*Real.pi*(q.2-1/2) at hb
  exact Prod.ext ((div_left_inj' Real.pi_ne_zero).mp ha)
    (by nlinarith [Real.pi_pos])

theorem areaPolarRadial_fderiv {p : Plane} (hp : 0 < p.1) (v : Plane) :
    fderiv ℝ areaPolarRadial p v =
      (v.1/(2*Real.pi*Real.sqrt (p.1/Real.pi)),2*Real.pi*v.2) := by
  have hq := ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).mul_const Real.pi⁻¹).sqrt
    (mul_pos hp (inv_pos.mpr Real.pi_pos)).ne'
  have ht := ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).sub_const (1/2:ℝ)).const_mul (2*Real.pi)
  change fderiv ℝ (fun q : Plane => (Real.sqrt (q.1/Real.pi),2*Real.pi*(q.2-1/2))) p v = _
  erw [(hq.prodMk ht).fderiv]
  ext <;> simp [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]

theorem areaPolar_det {p : Plane} (hp : 0 < p.1) : (fderiv ℝ areaPolar p).det = 1 := by
  have hr := Real.sqrt_pos.mpr (div_pos hp Real.pi_pos)
  have hd : (fderiv ℝ areaPolarRadial p).det =
      1/Real.sqrt (p.1/Real.pi) := by
    rw [planar_det,areaPolarRadial_fderiv hp,areaPolarRadial_fderiv hp,planarArea_apply]
    dsimp
    field_simp; norm_num
  have hdp : (fderiv ℝ polarCoord.symm (areaPolarRadial p)).det = Real.sqrt (p.1/Real.pi) := by
    rw [planar_det,polar_area]
    rfl
  change (fderiv ℝ (polarCoord.symm ∘ areaPolarRadial) p).det = _
  rw [fderiv_comp p (polar_smooth.differentiable (by simp) _)
    ((areaPolarRadial_smoothAt hp).differentiableAt (by simp)),
    ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,LinearMap.det_comp]
  change (fderiv ℝ polarCoord.symm (areaPolarRadial p)).det *
    (fderiv ℝ areaPolarRadial p).det = _
  rw [hdp,hd,mul_one_div_cancel hr.ne']

theorem areaPolar_capacity {p : Plane} (hp : 0 ≤ p.1) :
    Real.pi * radiusSq (areaPolar p) = p.1 := by
  have hs : (Real.sqrt (p.1/Real.pi))^2 = p.1/Real.pi :=
    Real.sq_sqrt (div_nonneg hp Real.pi_pos.le)
  have ht := Real.cos_sq_add_sin_sq (2*Real.pi*(p.2-1/2))
  change Real.pi * ((Real.sqrt (p.1/Real.pi)*Real.cos (2*Real.pi*(p.2-1/2)))^2+
    (Real.sqrt (p.1/Real.pi)*Real.sin (2*Real.pi*(p.2-1/2)))^2) = _
  calc
    _ = Real.pi*(Real.sqrt (p.1/Real.pi))^2 := by linear_combination Real.pi * (Real.sqrt (p.1/Real.pi))^2 * ht
    _ = p.1 := by rw [hs]; field_simp

theorem areaPolar_image_volume {S : Set Plane} (hS : MeasurableSet S)
    (hsub : S ⊆ areaPolarDomain) : volume (areaPolar '' S) = volume S := by
  have he := lintegral_abs_det_fderiv_eq_addHaar_image volume hS
    (f' := fderiv ℝ areaPolar)
    (fun x hx => ((areaPolar_smoothAt (hsub hx).1).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
    (areaPolar_injOn.mono hsub)
  rw [← he]
  calc
    (∫⁻ x in S, ENNReal.ofReal |(fderiv ℝ areaPolar x).det|) = ∫⁻ _ in S, (1 : ℝ≥0∞) := by
      apply setLIntegral_congr_fun hS
      intro x hx
      change ENNReal.ofReal |(fderiv ℝ areaPolar x).det| = 1
      rw [areaPolar_det (hsub hx).1]
      simp
    _ = volume S := by simp

 theorem HasCompactSupport.left_slice {F : Type*} [Zero F] {f : ℝ × ℝ → F}
    (hf : HasCompactSupport f) (y : ℝ) : HasCompactSupport (fun x => f (x,y)) := by
  apply HasCompactSupport.intro (hf.image continuous_fst)
  intro x hx
  by_contra hn
  exact hx ⟨(x,y),subset_tsupport f hn,rfl⟩

 theorem HasCompactSupport.right_slice {F : Type*} [Zero F] {f : ℝ × ℝ → F}
    (hf : HasCompactSupport f) (x : ℝ) : HasCompactSupport (fun y => f (x,y)) := by
  apply HasCompactSupport.intro (hf.image continuous_snd)
  intro y hy
  by_contra hn
  exact hy ⟨(x,y),subset_tsupport f hn,rfl⟩

 theorem integral_compact_partial_fst {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ z, fderiv ℝ f z (1,0))=0 := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (1,0)) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hdc := hc.fderiv_apply (𝕜 := ℝ) (1,0)
  rw [Measure.volume_eq_prod ℝ ℝ,integral_prod_symm _
    (hd.continuous.integrable_of_hasCompactSupport hdc)]
  have he (y : ℝ) : (∫ x, fderiv ℝ f (x,y) (1,0))=0 := by
    apply integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun x => f (x,y))
    · intro x
      exact ((hf.differentiable (by simp) (x,y)).hasFDerivAt).comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
    · exact (hd.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.left_slice hdc y)
    · exact (hf.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.left_slice hc y)
  simp_rw [he]
  exact integral_zero _ _

 theorem integral_compact_partial_snd {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ z, fderiv ℝ f z (0,1))=0 := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (0,1)) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hdc := hc.fderiv_apply (𝕜 := ℝ) (0,1)
  rw [Measure.volume_eq_prod ℝ ℝ,integral_prod _
    (hd.continuous.integrable_of_hasCompactSupport hdc)]
  have he (x : ℝ) : (∫ y, fderiv ℝ f (x,y) (0,1))=0 := by
    apply integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun y => f (x,y))
    · intro y
      exact ((hf.differentiable (by simp) (x,y)).hasFDerivAt).comp_hasDerivAt y
        ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
    · exact (hd.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.right_slice hdc x)
    · exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.right_slice hc x)
  simp_rw [he]
  exact integral_zero _ _

 theorem compact_planar_stokes {α : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (hc : HasCompactSupport α) :
    (∫ z, fderiv ℝ α z (1,0) (0,1) - fderiv ℝ α z (0,1) (1,0))=0 := by
  have h1 : ContDiff ℝ ∞ (fun z => α z (0,1)) := hα.clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun z => α z (1,0)) := hα.clm_apply contDiff_const
  have hc1 : HasCompactSupport (fun z => α z (0,1)) := hc.comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0,1)) rfl
  have hc2 : HasCompactSupport (fun z => α z (1,0)) := hc.comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1,0)) rfl
  have he1 (z v : ℝ × ℝ) : fderiv ℝ (fun z => α z (0,1)) z v=fderiv ℝ α z v (0,1) := by
    rw [fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _)]
    simp only [add_apply,ContinuousLinearMap.comp_apply,fderiv_const_apply,
      zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply]
  have he2 (z v : ℝ × ℝ) : fderiv ℝ (fun z => α z (1,0)) z v=fderiv ℝ α z v (1,0) := by
    rw [fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _)]
    simp only [add_apply,ContinuousLinearMap.comp_apply,fderiv_const_apply,
      zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply]
  have hd1 : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun z => α z (0,1)) z (1,0)) :=
    (h1.fderiv_right (by simp)).clm_apply contDiff_const
  have hd2 : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun z => α z (1,0)) z (0,1)) :=
    (h2.fderiv_right (by simp)).clm_apply contDiff_const
  simp_rw [← he1,← he2]
  rw [integral_sub
    (hd1.continuous.integrable_of_hasCompactSupport
      (hc1.fderiv_apply (𝕜 := ℝ) (1,0)))
    (hd2.continuous.integrable_of_hasCompactSupport
      (hc2.fderiv_apply (𝕜 := ℝ) (0,1))),
    integral_compact_partial_fst h1 hc1,integral_compact_partial_snd h2 hc2,sub_self]

theorem HasCompactSupport.comp_radiusSq {F : Type*} [Zero F] {g : ℝ → F}
    (hg : HasCompactSupport g) : HasCompactSupport (fun z : Plane => g (radiusSq z)) := by
  obtain ⟨B,hB,hbound⟩ := hg.isBounded.exists_pos_norm_le
  apply HasCompactSupport.intro ((isCompact_Icc : IsCompact (Icc (-(B+1)) (B+1))).prod (isCompact_Icc : IsCompact (Icc (-(B+1)) (B+1))))
  intro z hz
  by_contra hg0
  have hb := hbound (radiusSq z) (subset_tsupport g hg0)
  have hq : 0≤radiusSq z := add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg hq] at hb
  apply hz
  dsimp only [radiusSq] at hb
  constructor <;> constructor <;> nlinarith [sq_nonneg z.1,sq_nonneg z.2]

theorem HasCompactSupport.comp_square {F : Type*} [Zero F] {g : ℝ → F}
    (hg : HasCompactSupport g) : HasCompactSupport (fun x : ℝ => g (x^2)) := by
  simpa only [radiusSq,zero_pow (by decide : (2:ℕ)≠0),add_zero] using
    HasCompactSupport.left_slice (HasCompactSupport.comp_radiusSq hg) 0

theorem integral_radial_derivative {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : (∫ z : Plane,2*deriv g (radiusSq z))= -2*Real.pi*g 0 := by
  let h : ℝ → ℝ := fun r => g (r^2)
  have hh : ContDiff ℝ ∞ h := hg.comp (contDiff_id.pow 2)
  have hhC : HasCompactSupport h := HasCompactSupport.comp_square hc
  have hd (r : ℝ) : deriv h r=2*r*deriv g (r^2) := by
    have H := (hg.differentiable (by simp) (r^2)).hasDerivAt.comp r ((hasDerivAt_id r).pow 2)
    change HasDerivAt h _ r at H
    rw [H.deriv]
    simp only [Nat.cast_ofNat,mul_one,id_eq]
    norm_num
    ring
  rw [← integral_comp_polarCoord_symm]
  have he : (fun p : Plane => p.1 • (2*deriv g (radiusSq (polarCoord.symm p))))=
      (fun p : Plane => deriv h p.1 * (1 : ℝ)) := by
    funext p
    rw [radiusSq_polar,hd]
    simp only [smul_eq_mul]
    ring
  rw [he,polarCoord_target,Measure.volume_eq_prod,setIntegral_prod_mul (deriv h) (fun _ : ℝ => (1 : ℝ)),
    HasCompactSupport.integral_Ioi_deriv_eq (hh.of_le (by simp)) hhC]
  simp only [h,zero_pow (by decide : (2:ℕ)≠0),integral_const,smul_eq_mul,
    Measure.real,Measure.restrict_apply_univ,Real.volume_Ioo]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0≤Real.pi-(-Real.pi))]
  ring

def planarDot : Plane →L[ℝ] Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.fst ℝ ℝ ℝ)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) +
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem planarDot_apply (z v : Plane) : planarDot z v=z.1*v.1+z.2*v.2 := rfl

theorem radiusSq_hasFDerivAt (z : Plane) :
    HasFDerivAt radiusSq ((2:ℝ) • planarDot z) z := by
  have H := (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2).add
    (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2)
  change HasFDerivAt radiusSq _ z at H
  apply H.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  change (2 • z.1^(2-1))*v.1+(2 • z.2^(2-1))*v.2=2*(z.1*v.1+z.2*v.2)
  norm_num
  ring

def angularOneForm (z : Plane) : Plane →L[ℝ] ℝ := (radiusSq z)⁻¹ • planarArea z

theorem angularOneForm_contDiffAt {z : Plane} (hz : radiusSq z≠0) :
    ContDiffAt ℝ ∞ angularOneForm z :=
  (radiusSq_smooth.contDiffAt.inv hz).smul planarArea.contDiff.contDiffAt

theorem radialArea_curl {f : ℝ → ℝ} {z : Plane} (hf : DifferentiableAt ℝ f (radiusSq z)) :
    planarCurl (fun p : Plane => f (radiusSq p) • planarArea p) z=
      2*(f (radiusSq z)+radiusSq z*deriv f (radiusSq z)) := by
  have H := (hf.hasDerivAt.comp_hasFDerivAt z (radiusSq_hasFDerivAt z)).smul planarArea.hasFDerivAt
  change HasFDerivAt (fun p : Plane => f (radiusSq p) • planarArea p) _ z at H
  unfold planarCurl
  rw [H.fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,planarArea_apply,planarDot_apply,
    Function.comp_apply]
  dsimp only [radiusSq]
  ring

theorem cutoffAngular_curl {g : ℝ → ℝ} {z : Plane} (hg : DifferentiableAt ℝ g (radiusSq z))
    (hz : radiusSq z≠0) :
    planarCurl (fun p : Plane => g (radiusSq p) • angularOneForm p) z=
      2*deriv g (radiusSq z) := by
  have hd := hg.hasDerivAt.div (hasDerivAt_id (radiusSq z)) hz
  change HasDerivAt (fun t => g t / t) _ (radiusSq z) at hd
  have he : (fun p : Plane => g (radiusSq p) • angularOneForm p)=
      fun p => (g (radiusSq p)/radiusSq p) • planarArea p := by
    funext p
    simp only [angularOneForm,smul_smul,div_eq_mul_inv]
  rw [he,radialArea_curl hd.differentiableAt,hd.deriv]
  simp only [id_eq]
  field_simp
  ring

theorem integral_cutoffAngular_density {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (h0 : g 0=1) :
    (∫ z : Plane,2*deriv g (radiusSq z))= -2*Real.pi := by
  rw [integral_radial_derivative hg hc,h0,mul_one]

theorem planarCurl_contDiff {β : Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (planarCurl β) :=
  (((hβ.fderiv_right (by simp)).clm_apply contDiff_const).clm_apply contDiff_const).sub
    (((hβ.fderiv_right (by simp)).clm_apply contDiff_const).clm_apply contDiff_const)

theorem planarCurl_compact {β : Plane → Plane →L[ℝ] ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (planarCurl β) := by
  exact ((hβ.fderiv_apply (𝕜 := ℝ) (1,0)).comp_left
    (g := fun L : Plane →L[ℝ] ℝ => L (0,1)) rfl).sub
    ((hβ.fderiv_apply (𝕜 := ℝ) (0,1)).comp_left
    (g := fun L : Plane →L[ℝ] ℝ => L (1,0)) rfl)

def cutoffWedge (f : Plane → ℝ) (β : Plane → Plane →L[ℝ] ℝ) (z : Plane) : ℝ :=
  fderiv ℝ f z (1,0)*β z (0,1)-fderiv ℝ f z (0,1)*β z (1,0)

theorem planarCurl_spatial_smul {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {z : Plane}
    (hf : DifferentiableAt ℝ f z) (hβ : DifferentiableAt ℝ β z) :
    planarCurl (fun y => f y • β y) z=cutoffWedge f β z+f z*planarCurl β z := by
  unfold planarCurl cutoffWedge
  have H := hf.hasFDerivAt.smul hβ.hasFDerivAt
  change HasFDerivAt (fun y => f y • β y) _ z at H
  rw [H.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
  ring

theorem integral_cutoffWedge {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hβ : ContDiff ℝ ∞ β) :
    (∫ z,cutoffWedge f β z)= -(∫ z,f z*planarCurl β z) := by
  have hp : ContDiff ℝ ∞ (fun z => f z • β z) := hf.smul hβ
  have hpc : HasCompactSupport (fun z => f z • β z) := hc.smul_right
  have hci : Integrable (planarCurl (fun z => f z • β z)) := (planarCurl_contDiff hp).continuous.integrable_of_hasCompactSupport (planarCurl_compact hpc)
  have hgi : Integrable (fun z => f z*planarCurl β z) := (hf.mul (planarCurl_contDiff hβ)).continuous.integrable_of_hasCompactSupport hc.mul_right
  have he : cutoffWedge f β=(fun z => planarCurl (fun y => f y • β y) z-f z*planarCurl β z) := by
    funext z
    rw [planarCurl_spatial_smul (hf.differentiable (by simp) z) (hβ.differentiable (by simp) z)]
    ring
  rw [he,integral_sub hci hgi,show (∫ z,planarCurl (fun y => f y • β y) z)=0 from compact_planar_stokes hp hpc,zero_sub]

theorem cutoffWedge_integrable {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hβ : ContDiff ℝ ∞ β) :
    Integrable (cutoffWedge f β) := by
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (1,0)) := (hf.fderiv_right (by simp)).clm_apply (contDiff_const (c := ((1:ℝ),(0:ℝ))))
  have h2 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (0,1)) := (hf.fderiv_right (by simp)).clm_apply (contDiff_const (c := ((0:ℝ),(1:ℝ))))
  exact ((h1.mul (hβ.clm_apply contDiff_const)).continuous.integrable_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) (1,0)).mul_right).sub
    ((h2.mul (hβ.clm_apply contDiff_const)).continuous.integrable_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) (0,1)).mul_right)

theorem integral_planar_residue_cutoff {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (h0 : g 0=1)
    (hβ : ContDiff ℝ ∞ β) (c : ℝ) :
    (∫ z : Plane,-cutoffWedge (fun y => g (radiusSq y)) β z+c*deriv g (radiusSq z))=
      (∫ z : Plane,g (radiusSq z)*planarCurl β z)-c*Real.pi := by
  have hgs : ContDiff ℝ ∞ (fun z : Plane => g (radiusSq z)) := hg.comp radiusSq_smooth
  have hgc := HasCompactSupport.comp_radiusSq hc
  have hdi : Integrable (fun z : Plane => deriv g (radiusSq z)) := ((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.comp_radiusSq hc.deriv)
  have hni : Integrable (fun z : Plane => -cutoffWedge (fun y => g (radiusSq y)) β z) :=
    (cutoffWedge_integrable hgs hgc hβ).neg
  rw [integral_add hni (hdi.const_mul c),integral_neg,
    integral_cutoffWedge hgs hgc hβ,neg_neg,integral_const_mul]
  have hi := integral_radial_derivative hg hc
  rw [integral_const_mul,h0,mul_one] at hi
  have hid : (∫ z : Plane,deriv g (radiusSq z))= -Real.pi := by linarith
  rw [hid]
  ring

def shrinkingCutoff (g : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ := g (((n:ℝ)+1)*t)

theorem shrinkingCutoff_smooth {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    ContDiff ℝ ∞ (shrinkingCutoff g n) := hg.comp (contDiff_const.mul contDiff_id)

theorem shrinkingCutoff_compact {g : ℝ → ℝ} (hg : HasCompactSupport g) (n : ℕ) :
    HasCompactSupport (shrinkingCutoff g n) := by
  have hh := hg.comp_homeomorph (Homeomorph.smulOfNeZero (α := ℝ) ((n:ℝ)+1) (by positivity))
  change HasCompactSupport (fun t : ℝ => g (((n:ℝ)+1)*t))
  simpa only [Function.comp_def,Homeomorph.smulOfNeZero_apply,smul_eq_mul] using hh

theorem shrinkingCutoff_one {g : ℝ → ℝ} {r : ℝ}
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (n : ℕ) :
    ∀ t∈Ioo (-(r/((n:ℝ)+1))) (r/((n:ℝ)+1)),shrinkingCutoff g n t=1 := by
  intro t ht
  apply h1
  have hn : 0<(n:ℝ)+1 := by positivity
  constructor
  · have hh : (-r)/((n:ℝ)+1)<t := by simpa only [neg_div] using ht.1
    have h := (div_lt_iff₀ hn).mp hh
    linarith
  · have h := (lt_div_iff₀ hn).mp ht.2
    nlinarith

theorem shrinkingCutoff_tsupport {g : ℝ → ℝ} {R : ℝ}
    (hR : 0≤R) (h0 : tsupport g⊆Iic R) (n : ℕ) :
    tsupport (shrinkingCutoff g n)⊆Iic R := by
  apply closure_minimal _ isClosed_Iic
  intro t ht
  by_contra hn
  have htR : R<t := lt_of_not_ge hn
  have hnt : R<((n:ℝ)+1)*t := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  change g (((n:ℝ)+1)*t)≠0 at ht
  exact ht (image_eq_zero_of_notMem_tsupport (f := g) (fun hx => not_le_of_gt hnt (h0 hx)))

theorem shrinkingCutoff_eventually_zero {g : ℝ → ℝ} (hc : HasCompactSupport g)
    {t : ℝ} (ht : 0<t) : ∀ᶠ n in atTop,shrinkingCutoff g n t=0 := by
  obtain ⟨B,_hB,hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hz : ∀ᶠ s : ℝ in atTop,g s=0 := by
    filter_upwards [eventually_gt_atTop B] with s hs
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hb := hbound s h
    have hsn := le_abs_self s
    rw [Real.norm_eq_abs] at hb
    linarith
  have hseq : Tendsto (fun n : ℕ => ((n:ℝ)+1)*t) atTop atTop :=
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).atTop_mul_const ht
  exact hseq.eventually hz

theorem radiusSq_pos {z : Plane} (hz : z≠0) : 0<radiusSq z := by
  have hn := radiusSq_nonneg z
  by_contra hh
  have he : radiusSq z=0 := le_antisymm (le_of_not_gt hh) hn
  apply hz
  apply Prod.ext <;> change _=0 <;> dsimp only [radiusSq] at he <;>
    nlinarith [sq_nonneg z.1,sq_nonneg z.2]

theorem tendsto_shrinking_regular_residue {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hbound : ∀ t,g t∈Icc (0:ℝ) 1)
    {β : Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β) :
    Tendsto (fun n => ∫ z : Plane,shrinkingCutoff g n (radiusSq z)*planarCurl β z)
      atTop (𝓝 0) := by
  have hi : Integrable (planarCurl β) := (planarCurl_contDiff hβ).continuous.integrable_of_hasCompactSupport (planarCurl_compact hβc)
  have h := tendsto_integral_of_dominated_convergence (fun z => ‖planarCurl β z‖)
    (f := fun _ : Plane => (0:ℝ))
    (fun n => (((shrinkingCutoff_smooth hg n).comp radiusSq_smooth).mul
      (planarCurl_contDiff hβ)).continuous.aestronglyMeasurable) hi.norm
    (fun n => Filter.Eventually.of_forall (fun z => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by
        rw [Real.norm_eq_abs]
        change |g (((n:ℝ)+1)*radiusSq z)|≤1
        rw [abs_of_nonneg (hbound _).1]
        exact (hbound _).2))) (by
      have hne : ∀ᵐ z : Plane,z≠0 := by
        apply ae_iff.mpr
        simp
      filter_upwards [hne] with z hz
      apply tendsto_const_nhds.congr'
      filter_upwards [shrinkingCutoff_eventually_zero hc (radiusSq_pos hz)] with n hn
      change 0=shrinkingCutoff g n (radiusSq z)*planarCurl β z
      rw [hn,zero_mul])
  simpa only [integral_zero,Function.comp_apply] using h

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ,E) hK.isClosed hKL (n := ⊤)
  have hs : tsupport (χ : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hn
    exact hx (hχ0 x hn)
  exact ⟨χ,χ.contMDiff.contDiff,hL.of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans hLU,hχ1,hχrange⟩

theorem exists_smooth_compact_extension {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ x, χ x ∈ Icc 0 1) ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧
      ContDiff ℝ ∞ (fun x => χ x • f x) ∧
      HasCompactSupport (fun x => χ x • f x) ∧
      (∀ᶠ x in 𝓝ˢ K, χ x • f x = f x) := by
  obtain ⟨χ,hχ,hχc,hχU,hχ1,hχrange⟩ := exists_smooth_cutoff hK hU hKU
  have hg : ContDiff ℝ ∞ (fun x => χ x • f x) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul ((hf x hx).contDiffAt (hU.mem_nhds hx))
    · have hn : x ∉ tsupport χ := fun h => hx (hχU h)
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hn)
      apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      simp only [hy,zero_smul,Pi.zero_apply]
  have hs : tsupport (fun x => χ x • f x) ⊆ tsupport χ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    apply hx
    change χ x • f x = 0
    rw [image_eq_zero_of_notMem_tsupport hn,zero_smul]
  refine ⟨χ,hχ,hχc,hχU,hχrange,hχ1,hg,
    hχc.of_isClosed_subset (isClosed_tsupport _) hs,?_⟩
  filter_upwards [hχ1] with x hx
  rw [hx,one_smul]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem curveSigmaCompact : SigmaCompactSpace (locus a) :=
  IsClosed.sigmaCompactSpace (locus_isClosed a)

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem exists_end_cutoff : ∃ (g : ℝ → ℝ) (r R : ℝ),0<r ∧ 0<R ∧
    ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∀ t,g t∈Icc (0:ℝ) 1) ∧
    (∀ t∈Ioo (-r) r,g t=1) ∧ tsupport g⊆Iic R ∧
    {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a := by
  obtain ⟨d,hd,hdb⟩ := infinityRegion_contains_ball a
  let R := (d/2)^2
  have hR : 0<R := sq_pos_of_pos (by linarith)
  have hreg : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a := by
    intro s hs
    apply hdb
    rw [Metric.mem_ball,dist_zero_right]
    have hn : ‖s‖≤d/2 := (sq_le_sq₀ (norm_nonneg s) (by linarith : 0≤d/2)).mp (by
      simpa only [Complex.normSq_eq_norm_sq,R,mem_ofPred_eq] using hs)
    linarith
  obtain ⟨g,hg,hgc,hgs,hg1,hgb⟩ := exists_smooth_cutoff
    (isCompact_Icc : IsCompact (Icc (-R/2) (R/2))) isOpen_Ioo
    (show Icc (-R/2) (R/2)⊆Ioo (-R) R by intro t ht; constructor <;> linarith [ht.1,ht.2])
  refine ⟨g,R/2,R,by linarith,hR,hg,hgc,hgb,?_,?_,hreg⟩
  · intro t ht
    have he : g=ᶠ[𝓝 t] fun _ => 1 := hg1.filter_mono
      (nhds_le_nhdsSet (show t∈Icc (-R/2) (R/2) by
        constructor <;> linarith [ht.1,ht.2]))
    exact he.eq_of_nhds
  · exact fun t ht => (hgs ht).2.le

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem shrinking_curveEndCutoff_compact {g : ℝ → ℝ} {r : ℝ}
    (hr : 0<r) (h1 : ∀ t∈Ioo (-r) r,g t=1) (n : ℕ) :
    HasCompactSupport (curveEndCutoff a (shrinkingCutoff g n)) := by
  apply curveEndCutoff_compact a
  have hn : 0<r/((n:ℝ)+1) := div_pos hr (by positivity)
  filter_upwards [isOpen_Ioo.mem_nhds
    (show (0:ℝ)∈Ioo (-(r/((n:ℝ)+1))) (r/((n:ℝ)+1)) by constructor <;> linarith)] with t ht
  exact shrinkingCutoff_one h1 n t ht

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem curveEndCutoff_eventually_one_on_compact {g : ℝ → ℝ} {R : ℝ}
    (hR : 0≤R) (h0 : tsupport g⊆Iic R) {K : Set (locus a)} (hK : IsCompact K) :
    ∀ᶠ n in atTop,∀ x∈K,curveEndCutoff a (shrinkingCutoff g n) x=1 := by
  obtain ⟨B,hB,hbound⟩ := (hK.image (curveProjection_continuous a)).isBounded.exists_pos_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R*B^2)
  filter_upwards [eventually_ge_atTop N] with n hn
  intro x hx
  by_cases hz : curveProjection a x=0
  · simp only [curveEndCutoff,inverseComplementCutoff,hz,↓reduceIte]
  · have ht : Complex.normSq (curveProjection a x)>0 := Complex.normSq_pos.mpr hz
    have hb : Complex.normSq (curveProjection a x)≤B^2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact (sq_le_sq₀ (norm_nonneg _) hB.le).mpr (hbound _ ⟨x,hx,rfl⟩)
    have hnn : (N:ℝ)≤n := by exact_mod_cast hn
    have hnt : R<((n:ℝ)+1)*Complex.normSq ((curveProjection a x)⁻¹) := by
      rw [Complex.normSq_inv]
      apply (lt_mul_inv_iff₀ ht).mpr
      nlinarith [mul_le_mul_of_nonneg_left hb hR]
    have hg0 : g (((n:ℝ)+1)*Complex.normSq ((curveProjection a x)⁻¹))=0 :=
      image_eq_zero_of_notMem_tsupport (fun hg => not_le_of_gt hnt (h0 hg))
    simp only [curveEndCutoff,inverseComplementCutoff,hz,↓reduceIte,shrinkingCutoff,hg0,sub_zero]

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
