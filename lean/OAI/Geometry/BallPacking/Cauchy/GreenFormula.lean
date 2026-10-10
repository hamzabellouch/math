import Mathlib
import OAI.Geometry.BallPacking.Holder.HolderTaylor
import OAI.Geometry.BallPacking.Rigidity.RadialForm

namespace OAI

noncomputable section

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem plane_deriv_first {F : Plane → ℝ} (hF : Differentiable ℝ F) (p : Plane) :
    deriv (fun x => F (x,p.2)) p.1 = fderiv ℝ F p (1,0) := by
  exact ((hF p).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv

theorem plane_deriv_second {F : Plane → ℝ} (hF : Differentiable ℝ F) (p : Plane) :
    deriv (fun t => F (p.1,t)) p.2 = fderiv ℝ F p (0,1) := by
  exact ((hF p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv

def pullbackForm (phi : Plane → Plane) (alpha : Plane → Plane →L[ℝ] ℝ)
    (p : Plane) : Plane →L[ℝ] ℝ := (alpha (phi p)).comp (fderiv ℝ phi p)

theorem bilinear_skew_plane (B : Plane →L[ℝ] Plane →L[ℝ] ℝ) (u v : Plane) :
    B u v - B v u = (B (1,0) (0,1)-B (0,1) (1,0))*planarArea u v := by
  have hu : u = u.1 • ((1:ℝ),(0:ℝ)) + u.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  have hv : v = v.1 • ((1:ℝ),(0:ℝ)) + v.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  conv_lhs => rw [hu,hv]
  simp only [map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,planarArea_apply]
  ring

theorem pullbackForm_smooth {phi : Plane → Plane} (hp : ContDiff ℝ ∞ phi)
    {alpha : Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha) :
    ContDiff ℝ ∞ (pullbackForm phi alpha) :=
  (ha.comp hp).clm_comp (hp.fderiv_right (by simp))

theorem pullbackForm_curl {phi : Plane → Plane} (hp : ContDiff ℝ ∞ phi)
    {alpha : Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha) (p : Plane) :
    planarCurl (pullbackForm phi alpha) p = planarCurl alpha (phi p) *
      planarArea (fderiv ℝ phi p (1,0)) (fderiv ℝ phi p (0,1)) := by
  have hd := (((ha.differentiable (by simp)) (phi p)).hasFDerivAt.comp p
    (((hp.differentiable (by simp)) p).hasFDerivAt)).clm_comp
      (((hp.fderiv_right (by simp : (∞ : ℕ∞ω)+1 ≤ ∞)).differentiable (by simp) p).hasFDerivAt)
  have hs := (hp.contDiffAt (x := p)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  dsimp only [Function.comp_def] at hd
  unfold planarCurl pullbackForm
  rw [hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply]
  rw [hs.eq (1,0) (0,1)]
  have hb := bilinear_skew_plane (fderiv ℝ alpha (phi p))
    (fderiv ℝ phi p (1,0)) (fderiv ℝ phi p (0,1))
  linear_combination hb

theorem integral_curl_rectangle {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) (a b : Plane) (hab : a ≤ b) :
    (∫ p in Icc a b, planarCurl alpha p) =
      ((∫ t in a.2..b.2, alpha (b.1,t) (0,1)) - ∫ t in a.2..b.2, alpha (a.1,t) (0,1)) -
      ((∫ r in a.1..b.1, alpha (r,b.2) (1,0)) - ∫ r in a.1..b.1, alpha (r,a.2) (1,0)) := by
  let F : Plane → ℝ := fun p => alpha p (0,1)
  let G : Plane → ℝ := fun p => -alpha p (1,0)
  have hF : ContDiff ℝ ∞ F := ha.clm_apply contDiff_const
  have hG : ContDiff ℝ ∞ G := (ha.clm_apply contDiff_const).neg
  have hFd (p : Plane) : fderiv ℝ F p =
      (ContinuousLinearMap.apply ℝ ℝ (0,1)).comp (fderiv ℝ alpha p) :=
    ((ContinuousLinearMap.apply ℝ ℝ (0,1) : (Plane →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp p
      ((ha.differentiable (by simp)) p).hasFDerivAt).fderiv
  have hGd (p : Plane) : fderiv ℝ G p =
      -((ContinuousLinearMap.apply ℝ ℝ (1,0)).comp (fderiv ℝ alpha p)) :=
    (((ContinuousLinearMap.apply ℝ ℝ (1,0) : (Plane →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp p
      ((ha.differentiable (by simp)) p).hasFDerivAt).neg).fderiv
  have he (p : Plane) : fderiv ℝ F p (1,0)+fderiv ℝ G p (0,1) = planarCurl alpha p := by
    rw [hFd,hGd]
    rfl
  have hi : IntegrableOn (fun p => fderiv ℝ F p (1,0)+fderiv ℝ G p (0,1)) (Icc a b) :=
    (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).add
      ((hG.continuous_fderiv (by simp)).clm_apply continuous_const)).continuousOn.integrableOn_compact isCompact_Icc
  have hg := integral_divergence_prod_Icc_of_hasFDerivAt_of_le F G
    (fderiv ℝ F) (fderiv ℝ G) a b hab hF.continuous.continuousOn hG.continuous.continuousOn
    (fun p _ => ((hF.differentiable (by simp)) p).hasFDerivAt)
    (fun p _ => ((hG.differentiable (by simp)) p).hasFDerivAt) hi
  simp_rw [he] at hg
  simp only [F,G,intervalIntegral.integral_neg] at hg
  linear_combination hg

@[fun_prop] theorem polar_smooth : ContDiff ℝ ∞ (polarCoord.symm : Plane → Plane) := by
  change ContDiff ℝ ∞ (fun p : Plane => (p.1*Real.cos p.2,p.1*Real.sin p.2))
  fun_prop

theorem polar_deriv_first (p : Plane) :
    fderiv ℝ polarCoord.symm p (1,0) = (Real.cos p.2,Real.sin p.2) := by
  rw [(hasFDerivAt_polarCoord_symm p).fderiv]
  simp [fderivPolarCoordSymm,Matrix.toLin_finTwoProd_toContinuousLinearMap]

theorem polar_deriv_second (p : Plane) :
    fderiv ℝ polarCoord.symm p (0,1) = (-p.1*Real.sin p.2,p.1*Real.cos p.2) := by
  rw [(hasFDerivAt_polarCoord_symm p).fderiv]
  simp [fderivPolarCoordSymm,Matrix.toLin_finTwoProd_toContinuousLinearMap]

theorem polar_area (p : Plane) :
    planarArea (fderiv ℝ polarCoord.symm p (1,0)) (fderiv ℝ polarCoord.symm p (0,1)) = p.1 := by
  rw [polar_deriv_first,polar_deriv_second,planarArea_apply]
  have ht := Real.cos_sq_add_sin_sq p.2
  dsimp
  linear_combination p.1 * ht

theorem integral_curl_polar_rectangle {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) {R : ℝ} (hR : 0 ≤ R) :
    (∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), p.1*planarCurl alpha (polarCoord.symm p)) =
      ∫ t in -Real.pi..Real.pi,
        alpha (polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) := by
  let eta := pullbackForm polarCoord.symm alpha
  have he (p : Plane) : planarCurl eta p = p.1*planarCurl alpha (polarCoord.symm p) := by
    rw [pullbackForm_curl polar_smooth ha,polar_area,mul_comm]
  have h := integral_curl_rectangle (pullbackForm_smooth polar_smooth ha)
    ((0:ℝ),-Real.pi) (R,Real.pi) ⟨hR,by linarith [Real.pi_pos]⟩
  change (∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), planarCurl eta p) = _ at h
  simp_rw [he] at h
  have hside (r : ℝ) : eta (r,Real.pi) (1,0) = eta (r,-Real.pi) (1,0) := by
    simp [eta,pullbackForm,polar_deriv_first,polarCoord_symm_apply]
  have hin (t : ℝ) : eta (0,t) (0,1) = 0 := by
    simp [eta,pullbackForm,polar_deriv_second,Prod.mk_zero_zero]
  have hout (t : ℝ) : eta (R,t) (0,1) =
      alpha (polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) := by
    simp [eta,pullbackForm,polar_deriv_second]
  change _ = ((∫ t in -Real.pi..Real.pi, eta (R,t) (0,1)) -
    ∫ t in -Real.pi..Real.pi, eta (0,t) (0,1)) -
    ((∫ r in (0:ℝ)..R, eta (r,Real.pi) (1,0)) - ∫ r in (0:ℝ)..R, eta (r,-Real.pi) (1,0)) at h
  simp_rw [hside,hin,hout] at h
  simpa using h

def roundDisk (R : ℝ) : Set Plane := {p | p.1^2+p.2^2 < R^2}

theorem polar_mem_roundDisk {R : ℝ} (hR : 0 < R) {p : Plane} (hp : 0 < p.1) :
    polarCoord.symm p ∈ roundDisk R ↔ p.1 < R := by
  have hn : (polarCoord.symm p).1^2+(polarCoord.symm p).2^2 = p.1^2 := by
    simp only [polarCoord_symm_apply]
    linear_combination p.1^2 * Real.cos_sq_add_sin_sq p.2
  change (polarCoord.symm p).1^2+(polarCoord.symm p).2^2 < R^2 ↔ _
  rw [hn]
  constructor <;> intro h <;> nlinarith

theorem integral_roundDisk_polar (f : Plane → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ p in roundDisk R, f p) =
      ∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), p.1*f (polarCoord.symm p) := by
  have hm : MeasurableSet (roundDisk R) :=
    (isOpen_lt ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const).measurableSet
  let S : Set Plane := {p | p.1 < R}
  have hS : MeasurableSet S := (isOpen_lt continuous_fst continuous_const).measurableSet
  have he (p : Plane) (hp : p ∈ polarCoord.target) :
      p.1 * (roundDisk R).indicator f (polarCoord.symm p) =
        S.indicator (fun p => p.1*f (polarCoord.symm p)) p := by
    have hi := polar_mem_roundDisk hR hp.1
    by_cases ht : p.1 < R
    · simp only [indicator_of_mem (hi.mpr ht),indicator_of_mem (show p ∈ S from ht)]
    · simp only [indicator_of_notMem (mt hi.mp ht),indicator_of_notMem (show p ∉ S from ht),mul_zero]
  have hinter : polarCoord.target ∩ S = Ioo (0:ℝ) R ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [polarCoord_target,mem_inter_iff,mem_prod,mem_Ioi,mem_Ioo,S,mem_ofPred_eq]
    tauto
  calc
    (∫ p in roundDisk R, f p) = ∫ p in polarCoord.target,
        p.1 * (roundDisk R).indicator f (polarCoord.symm p) := by
      rw [← integral_indicator hm]
      exact (integral_comp_polarCoord_symm ((roundDisk R).indicator f)).symm
    _ = ∫ p in polarCoord.target, S.indicator (fun p => p.1*f (polarCoord.symm p)) p :=
      setIntegral_congr_fun polarCoord.open_target.measurableSet he
    _ = ∫ p in Ioo (0:ℝ) R ×ˢ Ioo (-Real.pi) Real.pi, p.1*f (polarCoord.symm p) := by
      rw [setIntegral_indicator hS,hinter]
    _ = ∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), p.1*f (polarCoord.symm p) := by
      apply setIntegral_congr_set
      rw [Icc_prod_eq]
      exact MeasureTheory.Measure.set_prod_ae_eq MeasureTheory.Ioo_ae_eq_Icc MeasureTheory.Ioo_ae_eq_Icc

theorem integral_curl_roundDisk {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) {R : ℝ} (hR : 0 < R) :
    (∫ p in roundDisk R, planarCurl alpha p) =
      ∫ t in -Real.pi..Real.pi,
        alpha (polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) := by
  rw [integral_roundDisk_polar _ hR]
  exact integral_curl_polar_rectangle ha hR.le

def coordinateForm (U V : Plane → ℝ) (p : Plane) : Plane →L[ℝ] ℝ :=
  U p • ContinuousLinearMap.fst ℝ ℝ ℝ + V p • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem coordinateForm_apply (U V : Plane → ℝ) (p v : Plane) :
    coordinateForm U V p v = U p*v.1+V p*v.2 := rfl

theorem coordinateForm_smooth {U V : Plane → ℝ} (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (coordinateForm U V) :=
  (hU.smul contDiff_const).add (hV.smul contDiff_const)

theorem coordinateForm_compact {U V : Plane → ℝ} (hU : HasCompactSupport U)
    (hV : HasCompactSupport V) : HasCompactSupport (coordinateForm U V) := by
  apply HasCompactSupport.intro (hU.union hV)
  intro p hp
  have hu : U p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (Or.inl h))
  have hv : V p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (Or.inr h))
  simp only [coordinateForm,hu,hv,zero_smul,zero_add]

theorem form_eval_fderiv {alpha : Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha)
    (p v w : Plane) : fderiv ℝ (fun q => alpha q w) p v = fderiv ℝ alpha p v w := by
  have he := ((ContinuousLinearMap.apply ℝ ℝ w : (Plane →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp p
    ((ha.differentiable (by simp)) p).hasFDerivAt).fderiv
  exact congrArg (fun D : Plane →L[ℝ] ℝ => D v) he

theorem coordinateForm_curl {U V : Plane → ℝ} (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) (p : Plane) :
    planarCurl (coordinateForm U V) p =
      deriv (fun x => V (x,p.2)) p.1 - deriv (fun y => U (p.1,y)) p.2 := by
  rw [plane_deriv_first (hV.differentiable (by simp)),
    plane_deriv_second (hU.differentiable (by simp))]
  unfold planarCurl
  rw [← form_eval_fderiv (coordinateForm_smooth hU hV),
    ← form_eval_fderiv (coordinateForm_smooth hU hV)]
  simp only [coordinateForm_apply,mul_zero,mul_one,zero_add,add_zero]

end SymplecticBallPacking.Hamiltonian

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

 theorem polar_complex_eq_circleMap (R t : ℝ) :
    Complex.equivRealProdCLM.symm (polarCoord.symm (R,t)) = circleMap 0 R t := by
  apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply,polarCoord_symm_apply,
    circleMap_zero_re,circleMap_zero_im,Complex.cos_ofReal_re,Complex.sin_ofReal_re]

 theorem angular_complex_eq_circleMap (R t : ℝ) :
    Complex.equivRealProdCLM.symm (-R*Real.sin t,R*Real.cos t) =
      Complex.I*circleMap 0 R t := by
  apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply,
    circleMap_zero_re,circleMap_zero_im,Complex.cos_ofReal_re,Complex.sin_ofReal_re]

 theorem roundDisk_measurable (R : ℝ) : MeasurableSet (roundDisk R) :=
  (isOpen_lt ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const).measurableSet

 def cauchyCurl (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.I * fderiv ℝ f z 1 - fderiv ℝ f z Complex.I

 theorem cauchyCurl_smooth {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (cauchyCurl f) :=
  (contDiff_const.mul ((hf.fderiv_right (by simp)).clm_apply contDiff_const)).sub
    ((hf.fderiv_right (by simp)).clm_apply contDiff_const)

 theorem cauchyCurl_compact {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (cauchyCurl f) :=
  ((hf.fderiv_apply (𝕜 := ℝ) 1).comp_left (g := fun z : ℂ => Complex.I*z) (by simp)).sub
    (hf.fderiv_apply (𝕜 := ℝ) Complex.I)

 def projectedCauchyForm (L : ℂ →L[ℝ] ℝ) (f : ℂ → ℂ) : Plane → Plane →L[ℝ] ℝ :=
  coordinateForm (fun p => L (f (Complex.equivRealProdCLM.symm p)))
    (fun p => L (Complex.I*f (Complex.equivRealProdCLM.symm p)))

 theorem projectedCauchyForm_smooth (L : ℂ →L[ℝ] ℝ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (projectedCauchyForm L f) := by
  exact coordinateForm_smooth
    (L.contDiff.comp (hf.comp Complex.equivRealProdCLM.symm.contDiff))
    (L.contDiff.comp (contDiff_const.mul (hf.comp Complex.equivRealProdCLM.symm.contDiff)))

 theorem projectedCauchyForm_compact (L : ℂ →L[ℝ] ℝ) {f : ℂ → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (projectedCauchyForm L f) := by
  have hc := hf.comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph
  exact coordinateForm_compact (hc.comp_left L.map_zero)
    (hc.comp_left (g := fun z : ℂ => L (Complex.I*z)) (by simp))

 theorem projectedCauchyForm_apply (L : ℂ →L[ℝ] ℝ) (f : ℂ → ℂ) (p v : Plane) :
    projectedCauchyForm L f p v =
      L (f (Complex.equivRealProdCLM.symm p)*Complex.equivRealProdCLM.symm v) := by
  have h (z : ℂ) : z*Complex.equivRealProdCLM.symm v =
      v.1 • z + v.2 • (Complex.I*z) := by
    apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply] <;> ring
  rw [h,map_add,map_smul,map_smul]
  simp only [projectedCauchyForm,coordinateForm_apply,smul_eq_mul]
  ring

 theorem projectedCauchyForm_curl (L : ℂ →L[ℝ] ℝ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (p : Plane) :
    planarCurl (projectedCauchyForm L f) p =
      L (cauchyCurl f (Complex.equivRealProdCLM.symm p)) := by
  have hb := (hf.differentiable (by simp) (Complex.equivRealProdCLM.symm p)).hasFDerivAt.comp
    p Complex.equivRealProdCLM.symm.hasFDerivAt
  have hu := L.hasFDerivAt.comp p hb
  have hv := L.hasFDerivAt.comp p (hb.const_mul Complex.I)
  have hU : ContDiff ℝ ∞ (fun p => L (f (Complex.equivRealProdCLM.symm p))) :=
    L.contDiff.comp (hf.comp Complex.equivRealProdCLM.symm.contDiff)
  have hV : ContDiff ℝ ∞ (fun p => L (Complex.I*f (Complex.equivRealProdCLM.symm p))) :=
    L.contDiff.comp (contDiff_const.mul (hf.comp Complex.equivRealProdCLM.symm.contDiff))
  rw [projectedCauchyForm,coordinateForm_curl hU hV,
    plane_deriv_first (hV.differentiable (by simp)),
    plane_deriv_second (hU.differentiable (by simp))]
  simp only [Function.comp_def] at hu hv
  rw [hu.fderiv,hv.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    smul_apply,smul_eq_mul,Complex.equivRealProdCLM_symm_apply,
    Complex.ofReal_one,Complex.ofReal_zero,zero_mul,one_mul,zero_add,add_zero]
  exact (map_sub L _ _).symm

 theorem complex_compact_stokes {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    (∫ p : Plane, cauchyCurl f (Complex.equivRealProdCLM.symm p)) = 0 := by
  have hi : Integrable (fun p : Plane => cauchyCurl f (Complex.equivRealProdCLM.symm p)) :=
    ((cauchyCurl_smooth hf).continuous.comp Complex.equivRealProdCLM.symm.continuous).integrable_of_hasCompactSupport
        ((cauchyCurl_compact hc).comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph)
  have hh (L : ℂ →L[ℝ] ℝ) : L (∫ p : Plane,
      cauchyCurl f (Complex.equivRealProdCLM.symm p))=0 := by
    rw [←L.integral_comp_comm hi]
    simp_rw [←projectedCauchyForm_curl L hf]
    exact compact_planar_stokes (projectedCauchyForm_smooth L hf)
      (projectedCauchyForm_compact L hc)
  exact Complex.ext (hh Complex.reCLM) (hh Complex.imCLM)

 theorem complex_disk_stokes {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {R : ℝ} (hR : 0<R) :
    (∫ p in roundDisk R, cauchyCurl f (Complex.equivRealProdCLM.symm p)) =
      ∫ t in -Real.pi..Real.pi, f (circleMap 0 R t)*(Complex.I*circleMap 0 R t) := by
  have hi : Integrable (fun p : Plane => cauchyCurl f (Complex.equivRealProdCLM.symm p)) :=
    ((cauchyCurl_smooth hf).continuous.comp Complex.equivRealProdCLM.symm.continuous).integrable_of_hasCompactSupport
        ((cauchyCurl_compact hc).comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph)
  have hb : IntervalIntegrable (fun t => f (circleMap 0 R t)*(Complex.I*circleMap 0 R t))
      volume (-Real.pi) Real.pi :=
    ((hf.continuous.comp (continuous_circleMap 0 R)).mul
      (continuous_const.mul (continuous_circleMap 0 R))).intervalIntegrable _ _
  have hh (L : ℂ →L[ℝ] ℝ) :
      L (∫ p in roundDisk R, cauchyCurl f (Complex.equivRealProdCLM.symm p)) =
      L (∫ t in -Real.pi..Real.pi, f (circleMap 0 R t)*(Complex.I*circleMap 0 R t)) := by
    rw [←L.integral_comp_comm hi.integrableOn,←L.intervalIntegral_comp_comm hb]
    simp_rw [←projectedCauchyForm_curl L hf]
    rw [integral_curl_roundDisk (projectedCauchyForm_smooth L hf) hR]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [projectedCauchyForm_apply,polar_complex_eq_circleMap,angular_complex_eq_circleMap]
  exact Complex.ext (hh Complex.reCLM) (hh Complex.imCLM)

 def cauchyInnerBump (R : ℝ) (hR : 0<R) : ContDiffBump (0:ℂ) where
  rIn := R/4
  rOut := R/2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

 def cauchyPuncture (b : ContDiffBump (0:ℂ)) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1-b z) • (f z/z)

 theorem cauchyPuncture_compact (b : ContDiffBump (0:ℂ)) {f : ℂ → ℂ}
    (hc : HasCompactSupport f) : HasCompactSupport (cauchyPuncture b f) := by
  apply HasCompactSupport.intro hc
  intro z hz
  simp only [cauchyPuncture,image_eq_zero_of_notMem_tsupport hz,zero_div,smul_zero]

 theorem cauchyPuncture_smooth (b : ContDiffBump (0:ℂ)) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (cauchyPuncture b f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z=0
  · subst z
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [b.eventuallyEq_one] with z hz
    simp only [cauchyPuncture,hz,Pi.one_apply,sub_self,zero_smul]
  · apply (contDiffAt_const.sub b.contDiff.contDiffAt).smul
    simpa only [div_eq_mul_inv] using hf.contDiffAt.mul (contDiffAt_inv (𝕜 := ℝ) hz)

 theorem cauchyPuncture_eventuallyEq (b : ContDiffBump (0:ℂ)) (f : ℂ → ℂ)
    {z : ℂ} (hz : b.rOut<‖z‖) :
    cauchyPuncture b f =ᶠ[𝓝 z] (fun w => f w/w) := by
  have hh : ∀ᶠ w in 𝓝 z, b.rOut<‖w‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  filter_upwards [hh] with w hw
  have hb : b w=0 := b.zero_of_le_dist (by simpa only [dist_zero_right] using hw.le)
  simp only [cauchyPuncture,hb,sub_zero,one_smul]

 theorem cauchyCurl_div {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hz : z≠0) : cauchyCurl (fun w => f w/w) z = cauchyCurl f z/z := by
  have hd := hf.hasFDerivAt.mul ((hasDerivAt_inv hz).hasFDerivAt.restrictScalars ℝ)
  have he : (fun w => f w/w) = (fun w => f w*w⁻¹) := by
    funext w
    exact div_eq_mul_inv _ _
  change HasFDerivAt (fun w => f w*w⁻¹) _ z at hd
  rw [he,cauchyCurl,hd.fderiv]
  change Complex.I * (f z * (1 * (-(z^2)⁻¹)) + z⁻¹ * fderiv ℝ f z 1) -
    (f z * (Complex.I * (-(z^2)⁻¹)) + z⁻¹ * fderiv ℝ f z Complex.I) =
      (Complex.I * fderiv ℝ f z 1 - fderiv ℝ f z Complex.I) / z
  rw [div_eq_mul_inv]
  ring

 theorem cauchyPuncture_curl (b : ContDiffBump (0:ℂ)) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) {z : ℂ} (hz : b.rOut<‖z‖) :
    cauchyCurl (cauchyPuncture b f) z = cauchyCurl f z/z := by
  have he := (cauchyPuncture_eventuallyEq b f hz).fderiv_eq (𝕜 := ℝ)
  unfold cauchyCurl
  rw [he]
  exact cauchyCurl_div (hf.differentiable (by simp) z)
    (fun h => by simp only [h,norm_zero,not_lt_of_ge b.rOut_pos.le] at hz)

 theorem complexCartesian_norm_sq (p : Plane) :
    ‖Complex.equivRealProdCLM.symm p‖^2 = p.1^2+p.2^2 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply,Complex.equivRealProdCLM_symm_apply,pow_two]

 theorem complexCartesian_norm_ge_of_notMem {R : ℝ} (hR : 0<R) {p : Plane}
    (hp : p ∉ roundDisk R) : R≤‖Complex.equivRealProdCLM.symm p‖ := by
  have hn := norm_nonneg (Complex.equivRealProdCLM.symm p)
  have he := complexCartesian_norm_sq p
  change ¬p.1^2+p.2^2<R^2 at hp
  push Not at hp
  nlinarith

 theorem cauchy_exterior_integral {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {R : ℝ} (hR : 0<R) :
    (∫ p in (roundDisk R)ᶜ,
      cauchyCurl f (Complex.equivRealProdCLM.symm p)/Complex.equivRealProdCLM.symm p) =
      -(Complex.I * ∫ t in -Real.pi..Real.pi, f (circleMap 0 R t)) := by
  let b := cauchyInnerBump R hR
  let g := cauchyPuncture b f
  have hg : ContDiff ℝ ∞ g := cauchyPuncture_smooth b hf
  have hgc : HasCompactSupport g := cauchyPuncture_compact b hc
  have hi : Integrable (fun p : Plane => cauchyCurl g (Complex.equivRealProdCLM.symm p)) :=
    ((cauchyCurl_smooth hg).continuous.comp Complex.equivRealProdCLM.symm.continuous).integrable_of_hasCompactSupport
        ((cauchyCurl_compact hgc).comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph)
  have hs := integral_add_compl (roundDisk_measurable R) hi
  rw [complex_compact_stokes hg hgc,complex_disk_stokes hg hgc hR] at hs
  have he : (∫ p in (roundDisk R)ᶜ, cauchyCurl g (Complex.equivRealProdCLM.symm p)) =
      ∫ p in (roundDisk R)ᶜ,
        cauchyCurl f (Complex.equivRealProdCLM.symm p)/Complex.equivRealProdCLM.symm p := by
    apply setIntegral_congr_fun (roundDisk_measurable R).compl
    intro p hp
    apply cauchyPuncture_curl b hf
    have hh := complexCartesian_norm_ge_of_notMem hR hp
    change R/2 < _
    linarith
  have hb : (∫ t in -Real.pi..Real.pi, g (circleMap 0 R t)*(Complex.I*circleMap 0 R t)) =
      Complex.I * ∫ t in -Real.pi..Real.pi, f (circleMap 0 R t) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    have hn : b.rOut<‖circleMap 0 R t‖ := by
      rw [norm_circleMap_zero,abs_of_pos hR]
      change R/2<R
      linarith
    rw [show g (circleMap 0 R t)=f (circleMap 0 R t)/circleMap 0 R t from
      (cauchyPuncture_eventuallyEq b f hn).eq_of_nhds]
    field_simp [circleMap_ne_center hR.ne' (θ := t)]
  rw [he,hb] at hs
  exact eq_neg_of_add_eq_zero_right hs

 theorem cauchyCurl_div_integrable {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : Integrable (fun z => cauchyCurl f z/z) := by
  simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using
    locallyIntegrable_complex_inv.integrable_smul_right_of_hasCompactSupport
      (cauchyCurl_smooth hf).continuous (cauchyCurl_compact hc)

 theorem shrinking_exterior_aecover :
    AECover (volume : Measure Plane) (𝓝[>] (0:ℝ)) (fun R => (roundDisk R)ᶜ) := by
  refine ⟨?_,fun R => (roundDisk_measurable R).compl⟩
  filter_upwards [volume.ae_ne (0:Plane)] with p hp
  have hpos : 0<p.1^2+p.2^2 := by
    by_contra! hh
    have hx : p.1=0 := by nlinarith [sq_nonneg p.1,sq_nonneg p.2]
    have hy : p.2=0 := by nlinarith [sq_nonneg p.1,sq_nonneg p.2]
    exact hp (Prod.ext hx hy)
  have hsq : ContinuousAt (fun R : ℝ => R^2) 0 := by fun_prop
  have ht : Tendsto (fun R : ℝ => R^2) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    simpa only [zero_pow (by decide : (2:ℕ)≠0)] using
      hsq.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  filter_upwards [ht.eventually (Iio_mem_nhds hpos)] with R hR
  change ¬p.1^2+p.2^2<R^2
  exact not_lt_of_ge (le_of_lt hR)

 theorem circle_mean_integral_limit {f : ℂ → ℂ} (hf : Continuous f) :
    Tendsto (fun R : ℝ => ∫ t in -Real.pi..Real.pi, f (circleMap 0 R t))
      (𝓝 (0:ℝ)) (𝓝 ((2*Real.pi : ℝ) • f 0)) := by
  have hh : Continuous (fun p : ℝ×ℝ => f (circleMap 0 p.1 p.2)) := by
    apply hf.comp
    unfold circleMap
    fun_prop
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun R t : ℝ => f (circleMap 0 R t)) hh (-Real.pi) Real.pi
  convert (hi.continuousAt (x := (0:ℝ))).tendsto using 1
  simp only [circleMap,Complex.ofReal_zero,zero_mul,zero_add,intervalIntegral.integral_const]
  congr 1
  congr 1
  ring

 theorem cauchy_green_fundamental {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    (∫ z : ℂ, cauchyCurl f z/z) = -(2*Real.pi*Complex.I)*f 0 := by
  have hp := Complex.volume_preserving_equiv_real_prod.symm
  have hi : Integrable (fun p : Plane =>
      cauchyCurl f (Complex.equivRealProdCLM.symm p)/Complex.equivRealProdCLM.symm p) :=
    hp.integrable_comp_of_integrable (cauchyCurl_div_integrable hf hc)
  have hl := ((circle_mean_integral_limit hf.continuous).const_mul Complex.I).neg
  have hl' : Tendsto (fun R : ℝ => ∫ p in (roundDisk R)ᶜ,
      cauchyCurl f (Complex.equivRealProdCLM.symm p)/Complex.equivRealProdCLM.symm p)
      (𝓝[>] (0:ℝ)) (𝓝 (-(2*Real.pi*Complex.I)*f 0)) := by
    have hh := hl.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    have heval : -(Complex.I * ((2*Real.pi:ℝ) • f 0)) =
        -(2*Real.pi*Complex.I)*f 0 := by
      rw [Complex.real_smul]
      push_cast
      ring
    rw [heval] at hh
    apply hh.congr'
    have hR : ∀ᶠ R in 𝓝[>] (0:ℝ), 0<R := self_mem_nhdsWithin
    filter_upwards [hR] with R hR
    exact (cauchy_exterior_integral hf hc hR).symm
  have he := shrinking_exterior_aecover.integral_eq_of_tendsto _ hi hl'
  rw [← hp.integral_comp' (fun z : ℂ => cauchyCurl f z/z)]
  exact he

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

def curlJet : (ℂ →L[ℝ] E) →L[ℝ] E :=
  Complex.I • ContinuousLinearMap.apply ℝ E (1:ℂ) - ContinuousLinearMap.apply ℝ E Complex.I

omit [CompleteSpace E] in
@[simp] lemma curlJet_apply (A : ℂ →L[ℝ] E) :
    curlJet A = Complex.I • A 1 - A Complex.I := rfl

omit [CompleteSpace E] in
lemma curlJet_smul (c : ℂ) (A : ℂ →L[ℝ] E) : curlJet (c • A) = c • curlJet A := by
  simp only [curlJet_apply, smul_apply, smul_sub]
  rw [smul_comm c Complex.I]

lemma smoothCauchyKernel_zero (z : ℂ) : smoothCauchyKernel 0 z = z⁻¹ := by
  rw [smoothCauchyKernel, add_zero, Complex.inv_def,Complex.normSq_eq_norm_sq]
  simp only [Complex.real_smul,Complex.ofReal_inv]
  exact mul_comm _ _

lemma regularizedCauchyJet_zero_fderiv {z : ℂ} (hz : z ≠ 0) :
    regularizedCauchyJet 0 z = fderiv ℝ (fun w : ℂ => w⁻¹) z := by
  have hd := ((hasDerivAt_inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))).comp_hasFDerivAt z
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt).smul
      (starL ℝ : ℂ ≃L[ℝ] ℂ).hasFDerivAt
  have he : (fun w : ℂ => (‖w‖^2)⁻¹ • star w) = fun w : ℂ => w⁻¹ := by
    funext w
    simpa only [smoothCauchyKernel, add_zero] using smoothCauchyKernel_zero w
  change HasFDerivAt (fun w : ℂ => (‖w‖^2)⁻¹ • star w) _ z at hd
  rw [he] at hd
  rw [hd.fderiv]
  ext v
  simp only [regularizedCauchyJet, add_zero, sub_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,starL'_apply,
    ContinuousLinearEquiv.coe_coe,add_apply,smul_smul,two_smul,Function.comp_apply]
  change (‖z‖^2)⁻¹ • star v - ((2/(‖z‖^2)^2)*(inner ℝ z v)) • star z =
    (‖z‖^2)⁻¹ • star v + (-((‖z‖^2)^2)⁻¹*(inner ℝ z v+inner ℝ z v)) • star z
  rw [sub_eq_add_neg, ← neg_smul]
  congr 2
  simp only [div_eq_mul_inv]
  ring

lemma regularizedCauchyJet_curl_zero {z : ℂ} (hz : z ≠ 0) :
    curlJet (regularizedCauchyJet 0 z) = (0:ℂ) := by
  rw [regularizedCauchyJet_zero_fderiv hz, curlJet_apply]
  have hd := (hasDerivAt_inv hz).hasFDerivAt.restrictScalars ℝ
  rw [hd.fderiv]
  change Complex.I * ((1:ℂ) * (-(z^2)⁻¹)) - Complex.I * (-(z^2)⁻¹) = 0
  ring

omit [CompleteSpace E] in
lemma cancellationJetIntegrand_integrable (b : ContDiffBump (0:ℂ))
    {g : ℂ → E} (hgC : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    Integrable (cancellationJetIntegrand b 0 g x) := by
  obtain ⟨C,hC,hCb⟩ := cutoff_smoothCauchyKernel_bound b
  let δ : ℕ → ℝ := fun n => 1/(n+1)
  have hδ (n : ℕ) : 0<δ n := by dsimp [δ]; positivity
  have hδt : Tendsto δ atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hδ⟩
  have hm : AEStronglyMeasurable (cancellationJetIntegrand b 0 g x) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (cancellationJetIntegrand_continuous b (hδ n) hgC x).aestronglyMeasurable)
      (Eventually.of_forall fun w => (cancellationJetIntegrand_tendsto b g x w).comp hδt)
  apply ((cauchySchauderWeight_integrable b.rOut).const_mul ((C+3)*H)).mono' hm
  apply Eventually.of_forall
  intro w
  apply le_of_tendsto (cancellationJetIntegrand_tendsto b g x w).norm
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact cancellationJetIntegrand_bound b hC hCb hH hg hd x w

def bumpCurlKernel (b : ContDiffBump (0:ℂ)) (w : ℂ) : ℂ :=
  cauchyCurl (fun z : ℂ => (b z : ℂ)) w / w

lemma bump_complex_smooth (b : ContDiffBump (0:ℂ)) :
    ContDiff ℝ ∞ (fun z : ℂ => (b z : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff

lemma bump_complex_compact (b : ContDiffBump (0:ℂ)) :
    HasCompactSupport (fun z : ℂ => (b z : ℂ)) := b.hasCompactSupport.comp_left (g := (Complex.ofReal : ℝ → ℂ)) (by simp)

lemma bumpCurlKernel_apply (b : ContDiffBump (0:ℂ)) (z : ℂ) :
    bumpCurlKernel b z =
      (Complex.I * (fderiv ℝ b z 1 : ℂ) - (fderiv ℝ b z Complex.I : ℂ)) * z⁻¹ := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z (((b.contDiff : ContDiff ℝ ∞ b).differentiable (by simp)) z).hasFDerivAt
  change HasFDerivAt (fun w : ℂ => (b w : ℂ)) _ z at hd
  rw [bumpCurlKernel,cauchyCurl,hd.fderiv,div_eq_mul_inv]
  rfl

lemma bumpCurlKernel_integrable (b : ContDiffBump (0:ℂ)) : Integrable (bumpCurlKernel b) :=
  cauchyCurl_div_integrable (bump_complex_smooth b) (bump_complex_compact b)

lemma bumpCurlKernel_integral (b : ContDiffBump (0:ℂ)) :
    (∫ w : ℂ, bumpCurlKernel b w) = -(2*Real.pi*Complex.I) := by
  have h := cauchy_green_fundamental (bump_complex_smooth b) (bump_complex_compact b)
  simpa only [bumpCurlKernel, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), Complex.ofReal_one, mul_one] using h

lemma cutoffCauchyJet_curl (b : ContDiffBump (0:ℂ)) {z : ℂ} (hz : z ≠ 0) :
    curlJet (cutoffCauchyJet b 0 z) = bumpCurlKernel b z := by
  rw [cutoffCauchyJet, map_add, map_smul,regularizedCauchyJet_curl_zero hz,smul_zero,zero_add]
  rw [curlJet_apply, smoothCauchyKernel_zero,bumpCurlKernel_apply]
  simp only [ContinuousLinearMap.smulRight_apply, Complex.real_smul,smul_eq_mul]
  ring

lemma tailCauchyJet_curl {z : ℂ} (hz : z ≠ 0) :
    curlJet (tailCauchyJet 0 z) = -bumpCurlKernel schauderBump z := by
  have he : scaledSchauderBump 1 = schauderBump := by funext w; simp [scaledSchauderBump]
  rw [tailCauchyJet,he,map_sub,map_smul,regularizedCauchyJet_curl_zero hz,smul_zero,zero_sub]
  rw [curlJet_apply,smoothCauchyKernel_zero,bumpCurlKernel_apply]
  simp only [ContinuousLinearMap.smulRight_apply, Complex.real_smul,smul_eq_mul]
  ring

omit [CompleteSpace E] in
lemma curlJet_smulComp (A : ℂ →L[ℝ] ℂ) (v : E) :
    curlJet (((ContinuousLinearMap.lsmul ℝ ℂ).flip v).comp A) = curlJet A • v := by
  simp only [curlJet_apply, ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, smul_smul,sub_smul,smul_eq_mul]

lemma cutoffCauchyDerivative_curl (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hgC : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    curlJet (cutoffCauchyDerivative b g x) =
      ∫ w : ℂ, bumpCurlKernel b w • (g (x-w)-g x) := by
  rw [cutoffCauchyDerivative, ← (curlJet (E := E)).integral_comp_comm
    (cancellationJetIntegrand_integrable b hgC hH hg x)]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0:ℂ)] with w hw
  rw [cancellationJetIntegrand,curlJet_smulComp,cutoffCauchyJet_curl b hw]

omit [CompleteSpace E] in
lemma tailIntegralJet_integrable {g : ℂ → E} (hgC : Continuous g) (hi : Integrable g) (x : ℂ) :
    Integrable (tailIntegralJet g x) := by
  obtain ⟨A,B,hA,hB,hjet,hL⟩ := tailCauchyKernel_bounds
  exact (hi.norm.const_mul A).mono' (tailIntegralJet_continuous hgC x).aestronglyMeasurable
    (Eventually.of_forall fun w => tailIntegralJet_bound hA (fun z => (hjet z).2) g x w)

lemma tailCauchyDerivative_curl {g : ℂ → E} (hgC : Continuous g) (hi : Integrable g) (x : ℂ) :
    curlJet (tailCauchyDerivative g x) = -(∫ w : ℂ, bumpCurlKernel schauderBump w • g (x-w)) := by
  rw [tailCauchyDerivative, ← (curlJet (E := E)).integral_comp_comm (tailIntegralJet_integrable hgC hi x)]
  rw [← integral_sub_left_eq_self _ volume x]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0:ℂ)] with w hw
  rw [tailIntegralJet,curlJet_smulComp,sub_sub_cancel,tailCauchyJet_curl hw,neg_smul]

omit [CompleteSpace E] in
lemma bumpCurlKernel_smul_integrable (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hgC : Continuous g) (x : ℂ) : Integrable (fun w : ℂ => bumpCurlKernel b w • g (x-w)) := by
  have hc := cauchyCurl_compact (bump_complex_compact b)
  have hs := cauchyCurl_smooth (bump_complex_smooth b)
  have hi := locallyIntegrable_complex_inv.integrable_smul_right_of_hasCompactSupport
    (hs.continuous.smul (hgC.comp (continuous_const.sub continuous_id)))
    (hc.smul_right (f' := fun w => g (x-w)))
  convert! hi using 1
  funext w
  change (cauchyCurl (fun z : ℂ => (b z : ℂ)) w / w) • g (x-w) =
    w⁻¹ • (cauchyCurl (fun z : ℂ => (b z : ℂ)) w • g (x-w))
  rw [div_eq_mul_inv,smul_smul,mul_comm]

lemma globalCauchyDerivative_curl {g : ℂ → E} (hgC : Continuous g) (hi : Integrable g)
    {H : ℝ} (hH : 0 ≤ H) (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    curlJet (globalCauchyDerivative g x) = (2*Complex.I) • g x := by
  rw [globalCauchyDerivative,curlJet_smul,map_add,
    cutoffCauchyDerivative_curl schauderBump hgC hH hg x,tailCauchyDerivative_curl hgC hi x]
  simp_rw [smul_sub]
  rw [integral_sub (bumpCurlKernel_smul_integrable schauderBump hgC x)
      ((bumpCurlKernel_integrable schauderBump).smul_const (g x)),integral_smul_const,
    bumpCurlKernel_integral]
  have he : (∫ w : ℂ, bumpCurlKernel schauderBump w • g (x-w)) -
      (-(2*Real.pi*Complex.I)) • g x + -(∫ w : ℂ, bumpCurlKernel schauderBump w • g (x-w)) =
      (2*Real.pi*Complex.I) • g x := by rw [neg_smul]; abel
  rw [he,smul_smul]
  congr 1
  field_simp [Real.pi_ne_zero]

lemma cauchyTransform_holder_curl {g : ℂ → E} (hgC : Continuous g) (hi : Integrable g)
    {H : ℝ} (hH : 0 ≤ H) (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    Complex.I • fderiv ℝ (cauchyTransform g) x 1 -
      fderiv ℝ (cauchyTransform g) x Complex.I = (2*Complex.I) • g x := by
  rw [(cauchyTransform_holder_hasFDerivAt hgC hi hH hg x).fderiv]
  exact globalCauchyDerivative_curl hgC hi hH hg x

end HigherDimensionalBallPacking.Rigidity
end

end OAI
