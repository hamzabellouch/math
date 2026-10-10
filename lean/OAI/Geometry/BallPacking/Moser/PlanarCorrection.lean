import Mathlib
import OAI.Geometry.BallPacking.Flows.TimeSteps

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Metric
open MeasureTheory Function
open scoped Classical
theorem exists_compact_planar_primitive {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hf0 : (∫ p, f p) = 0) :
    ∃ U V : ℝ × ℝ → ℝ, ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ V ∧
      HasCompactSupport U ∧ HasCompactSupport V ∧
      ∀ p, deriv (fun x => V (x,p.2)) p.1 - deriv (fun t => U (p.1,t)) p.2 = f p := by
  obtain ⟨A,hA,hbound⟩ := hfc.isBounded.subset_ball_lt 1 (0 : ℝ × ℝ)
  have hA0 : 0 < A := lt_trans zero_lt_one hA
  have hfs (x t : ℝ) (ht : A ≤ |x| ∨ A ≤ |t|) : f (x,t) = 0 := by
    by_contra hn
    have hb := hbound (subset_tsupport f (show (x,t) ∈ support f from hn))
    simp only [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      max_lt_iff] at hb
    rcases ht with ht | ht
    · exact (not_lt_of_ge ht) hb.1
    · exact (not_lt_of_ge ht) hb.2
  let b : ContDiffBump (0 : ℝ) := ⟨A/2,A,by positivity,by linarith⟩
  let ρ := b.normed volume
  have hρ : ContDiff ℝ ∞ ρ := b.contDiff_normed
  have hρs (x : ℝ) (hx : A ≤ |x|) : ρ x = 0 := by
    by_contra hn
    have hb : x ∈ support (b.normed volume) := hn
    rw [b.support_normed_eq] at hb
    have hb' : |x| < A := by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hb
    exact (not_lt_of_ge hx) hb'
  have hρ1 : (∫ x in -A..A, ρ x) = 1 := by
    rw [integral_eq_full_of_box_support hρs]
    exact b.integral_normed
  have hg : ContDiff ℝ ∞ (planarMarginal A f) := planarMarginal_smooth hf A
  have hgt (t : ℝ) (ht : A ≤ |t|) : planarMarginal A f t = 0 := by
    unfold planarMarginal
    have he : (fun x => f (x,t)) = fun _ => (0:ℝ) := funext (fun x => hfs x t (Or.inr ht))
    rw [he,intervalIntegral.integral_zero]
  have hgm (t : ℝ) : planarMarginal A f t = ∫ x, f (x,t) :=
    integral_eq_full_of_box_support (fun x hx => hfs x t (Or.inl hx))
  have hgm0 : (∫ t in -A..A, planarMarginal A f t) = 0 := by
    rw [integral_eq_full_of_box_support hgt]
    simp_rw [hgm]
    rw [← integral_prod_symm f]
    · exact hf0
    · exact hf.continuous.integrable_of_hasCompactSupport hfc
  obtain ⟨hU,hV⟩ := planarPrimitive_support hA0.le hf.continuous hρ.continuous
    hfs hρs hρ1 hg.continuous hgm0
  refine ⟨planarPrimitiveX A f ρ,planarPrimitiveY A f ρ,?_,?_,hU,hV,?_⟩
  · exact (planarPrimitive_smooth hf hρ A).1
  · exact (planarPrimitive_smooth hf hρ A).2
  · exact fun p => planarPrimitive_curl hf.continuous hρ.continuous hg.continuous p

abbrev Plane := ℝ × ℝ

def planarArea : Plane →L[ℝ] Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.fst ℝ ℝ ℝ)
    (ContinuousLinearMap.snd ℝ ℝ ℝ) -
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (ContinuousLinearMap.fst ℝ ℝ ℝ)

@[simp] theorem planarArea_apply (v w : Plane) : planarArea v w = v.1*w.2-v.2*w.1 := rfl

theorem planarArea_trace_identity (A : Plane →L[ℝ] Plane) (v w : Plane) :
    planarArea (A v) w + planarArea v (A w) =
      ((A (1,0)).1+(A (0,1)).2) * planarArea v w := by
  have hv : v = v.1 • ((1:ℝ),(0:ℝ)) + v.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  have hw : w = w.1 • ((1:ℝ),(0:ℝ)) + w.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  have ha : A v = v.1 • A (1,0) + v.2 • A (0,1) := by conv_lhs => rw [hv]; rw [map_add,map_smul,map_smul]
  have hb : A w = w.1 • A (1,0) + w.2 • A (0,1) := by conv_lhs => rw [hw]; rw [map_add,map_smul,map_smul]
  simp only [planarArea_apply,ha,hb,Prod.fst_add,Prod.snd_add,Prod.smul_def,smul_eq_mul]
  ring

theorem smoothTransition_deriv_compact : HasCompactSupport (deriv Real.smoothTransition) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := 1))
  intro t ht
  have hor : t < 0 ∨ 1 < t := by simpa only [mem_Icc,not_and_or,not_le] using ht
  rcases hor with ht | ht
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact Real.smoothTransition.zero_of_nonpos hs.le
    exact ((hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq he).deriv
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact Real.smoothTransition.one_of_one_le hs.le
    exact ((hasDerivAt_const t (1:ℝ)).congr_of_eventuallyEq he).deriv

def moserDensity (f : Plane → ℝ) (p : ℝ × Plane) : ℝ :=
  1 + Real.smoothTransition p.1 * f p.2

theorem moserDensity_positive {f : Plane → ℝ} (hf : ∀ x, 0 < 1+f x) (p : ℝ × Plane) :
    0 < moserDensity f p := by
  have hb := Real.smoothTransition.nonneg p.1
  have hc := Real.smoothTransition.le_one p.1
  unfold moserDensity
  by_cases hx : 0 ≤ f p.2
  · positivity
  · have hx' : f p.2 < 0 := lt_of_not_ge hx
    have hmul := mul_le_mul_of_nonpos_right hc hx'.le
    nlinarith [hf p.2]

theorem moserDensity_smooth {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (moserDensity f) :=
  contDiff_const.add ((Real.smoothTransition.contDiff.comp contDiff_fst).mul (hf.comp contDiff_snd))

def moserField (f U V : Plane → ℝ) (p : ℝ × Plane) : Plane :=
  (-(deriv Real.smoothTransition p.1) * V p.2 / moserDensity f p,
    (deriv Real.smoothTransition p.1) * U p.2 / moserDensity f p)

theorem moserField_smooth {f U V : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (hpos : ∀ x, 0 < 1+f x) :
    ContDiff ℝ ∞ (moserField f U V) := by
  have hβ : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  exact (((hβ.comp contDiff_fst).neg.mul (hV.comp contDiff_snd)).div
    (moserDensity_smooth hf) (fun p => (moserDensity_positive hpos p).ne')).prodMk
    (((hβ.comp contDiff_fst).mul (hU.comp contDiff_snd)).div
      (moserDensity_smooth hf) (fun p => (moserDensity_positive hpos p).ne'))

theorem moserField_hasCompactSupport {f U V : Plane → ℝ}
    (hU : HasCompactSupport U) (hV : HasCompactSupport V) : HasCompactSupport (moserField f U V) := by
  apply HasCompactSupport.intro (smoothTransition_deriv_compact.prod (hU.union hV))
  intro p hp
  have hn : p.1 ∉ tsupport (deriv Real.smoothTransition) ∨ p.2 ∉ tsupport U ∪ tsupport V := by
    simpa only [mem_prod, not_and_or] using hp
  rcases hn with ht | hx
  · simp [moserField, image_eq_zero_of_notMem_tsupport ht]
  · have hUx : U p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h))
    have hVx : V p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))
    simp [moserField,hUx,hVx]

theorem plane_deriv_first {F : Plane → ℝ} (hF : Differentiable ℝ F) (p : Plane) :
    deriv (fun x => F (x,p.2)) p.1 = fderiv ℝ F p (1,0) := by
  exact ((hF p).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv

theorem plane_deriv_second {F : Plane → ℝ} (hF : Differentiable ℝ F) (p : Plane) :
    deriv (fun t => F (p.1,t)) p.2 = fderiv ℝ F p (0,1) := by
  exact ((hF p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv

theorem hasDerivAt_horizontal_first {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × Plane → E} (hF : Differentiable ℝ F) (p : ℝ × Plane) :
    HasDerivAt (fun x => F (p.1,(x,p.2.2))) (fderiv ℝ F p (0,(1,0))) p.2.1 :=
  (hF p).hasFDerivAt.comp_hasDerivAt p.2.1 ((hasDerivAt_const p.2.1 p.1).prodMk
    ((hasDerivAt_id p.2.1).prodMk (hasDerivAt_const p.2.1 p.2.2)))

theorem hasDerivAt_horizontal_second {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × Plane → E} (hF : Differentiable ℝ F) (p : ℝ × Plane) :
    HasDerivAt (fun y => F (p.1,(p.2.1,y))) (fderiv ℝ F p (0,(0,1))) p.2.2 :=
  (hF p).hasFDerivAt.comp_hasDerivAt p.2.2 ((hasDerivAt_const p.2.2 p.1).prodMk
    ((hasDerivAt_const p.2.2 p.2.1).prodMk (hasDerivAt_id p.2.2)))

theorem moserField_transport {f U V : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (hpos : ∀ x, 0 < 1+f x)
    (hcurl : ∀ p, deriv (fun x => V (x,p.2)) p.1 - deriv (fun t => U (p.1,t)) p.2 = f p)
    (p : ℝ × Plane) (v w : Plane) :
    fderiv ℝ (moserDensity f) p (1,moserField f U V p) * planarArea v w +
      moserDensity f p * (planarArea (fderiv ℝ (moserField f U V) p (0,v)) w +
        planarArea v (fderiv ℝ (moserField f U V) p (0,w))) = 0 := by
  let X := moserField f U V
  let ρ := moserDensity f
  let b := deriv Real.smoothTransition p.1
  let d := fderiv ℝ ρ p
  let A := (fderiv ℝ X p).comp (ContinuousLinearMap.inr ℝ ℝ Plane)
  have hXd : Differentiable ℝ X := (moserField_smooth hf hU hV hpos).differentiable (by simp)
  have hρd : Differentiable ℝ ρ := (moserDensity_smooth hf).differentiable (by simp)
  have hUd : Differentiable ℝ U := hU.differentiable (by simp)
  have hVd : Differentiable ℝ V := hV.differentiable (by simp)
  have hflux1 : d (0,(1,0)) * (X p).1 + ρ p * (A (1,0)).1 =
      -b * fderiv ℝ V p.2 (1,0) := by
    have hd := (hasDerivAt_horizontal_first hρd p).mul (hasDerivAt_horizontal_first hXd p).fst
    have he : (fun x => ρ (p.1,(x,p.2.2)) * (X (p.1,(x,p.2.2))).1) =
        fun x => -b * V (x,p.2.2) := by
      funext x
      dsimp [X,ρ,moserField,b]
      field_simp [(moserDensity_positive hpos (p.1,(x,p.2.2))).ne']
    change HasDerivAt (fun x => ρ (p.1,(x,p.2.2)) * (X (p.1,(x,p.2.2))).1) _ p.2.1 at hd
    rw [he] at hd
    have hd' := ((hVd p.2).hasFDerivAt.comp_hasDerivAt p.2.1
      ((hasDerivAt_id p.2.1).prodMk (hasDerivAt_const p.2.1 p.2.2))).const_mul (-b)
    exact hd.unique hd'
  have hflux2 : d (0,(0,1)) * (X p).2 + ρ p * (A (0,1)).2 =
      b * fderiv ℝ U p.2 (0,1) := by
    have hd := (hasDerivAt_horizontal_second hρd p).mul (hasDerivAt_horizontal_second hXd p).snd
    have he : (fun y => ρ (p.1,(p.2.1,y)) * (X (p.1,(p.2.1,y))).2) =
        fun y => b * U (p.2.1,y) := by
      funext y
      dsimp [X,ρ,moserField,b]
      field_simp [(moserDensity_positive hpos (p.1,(p.2.1,y))).ne']
    change HasDerivAt (fun y => ρ (p.1,(p.2.1,y)) * (X (p.1,(p.2.1,y))).2) _ p.2.2 at hd
    rw [he] at hd
    have hd' := ((hUd p.2).hasFDerivAt.comp_hasDerivAt p.2.2
      ((hasDerivAt_const p.2.2 p.2.1).prodMk (hasDerivAt_id p.2.2))).const_mul b
    exact hd.unique hd'
  have ht : d (1,(0,0)) = b * f p.2 := by
    have hd := (hρd p).hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
    have hβ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
    have hb := (hβ.differentiable (by simp) p.1).hasDerivAt
    have hd' := (hb.mul_const (f p.2)).const_add 1
    exact hd.unique hd'
  have hc : fderiv ℝ V p.2 (1,0) - fderiv ℝ U p.2 (0,1) = f p.2 := by
    simpa only [plane_deriv_first hVd,plane_deriv_second hUd] using hcurl p.2
  have hlin : d (1,X p) = d (1,(0,0)) + (X p).1 * d (0,(1,0)) + (X p).2 * d (0,(0,1)) := by
    have he : ((1:ℝ),X p) = ((1:ℝ),(0:Plane)) +
        (X p).1 • ((0:ℝ),((1:ℝ),(0:ℝ))) + (X p).2 • ((0:ℝ),((0:ℝ),(1:ℝ))) := by
      ext <;> simp
    conv_lhs => rw [he]
    simp only [map_add,map_smul,smul_eq_mul]
    rfl
  have hdiv : d (1,X p) + ρ p * ((A (1,0)).1+(A (0,1)).2) = 0 := by
    rw [hlin]
    linear_combination hflux1 + hflux2 + ht - b * hc
  change d (1,X p) * planarArea v w + ρ p * (planarArea (A v) w + planarArea v (A w)) = 0
  rw [planarArea_trace_identity]
  linear_combination (planarArea v w) * hdiv

theorem exists_planar_moser_correction {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hf0 : (∫ p, f p) = 0) (hpos : ∀ x, 0 < 1+f x) :
    ∃ Φ : Plane ≃ₜ Plane, ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
      HasCompactSupport (fun x => Φ x - x) ∧
      ∀ x v w, (1+f (Φ x)) * planarArea (fderiv ℝ Φ x v) (fderiv ℝ Φ x w) = planarArea v w := by
  obtain ⟨U,V,hU,hV,hUc,hVc,hcurl⟩ := exists_compact_planar_primitive hf hfc hf0
  have hXs := moserField_smooth hf hU hV hpos
  have hXc := moserField_hasCompactSupport (f := f) hUc hVc
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by simp)
  let X : C(ℝ × Plane,Plane) := ⟨moserField f U V,hXs.continuous⟩
  let K := tsupport U ∪ tsupport V
  have hK : IsCompact K := hUc.union hVc
  have hfix (t : ℝ) (x : Plane) (hx : x ∉ K) : X (t,x) = 0 := by
    have hu : U x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h))
    have hv : V x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))
    change moserField f U V (t,x) = 0
    simp [moserField,hu,hv]
  obtain ⟨Φ,hΦ,hΦi,_,hΦc,hΦarea⟩ := exists_density_transport X hL hXs
    (moserDensity f) (moserDensity_smooth hf) planarArea
    (moserField_transport hf hU hV hpos hcurl) K hK hfix 0 1
  refine ⟨Φ,hΦ,hΦi,hΦc,?_⟩
  intro x v w
  simpa only [zero_add,moserDensity,Real.smoothTransition.one,Real.smoothTransition.zero,
    one_mul,zero_mul,add_zero] using hΦarea x v w

def planarCurl (alpha : Plane → Plane →L[ℝ] ℝ) (p : Plane) : ℝ :=
  fderiv ℝ alpha p (1,0) (0,1) - fderiv ℝ alpha p (0,1) (1,0)

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

def periodicPrimitive (a : ℝ → ℝ) (t : ℝ) := ∫ s in -Real.pi..t, a s

theorem periodicPrimitive_hasDerivAt {a : ℝ → ℝ} (ha : Continuous a) (t : ℝ) :
    HasDerivAt (periodicPrimitive a) (a t) t := by
  exact intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable _ _)
    ha.aestronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt

theorem periodicPrimitive_smooth {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (periodicPrimitive a) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (periodicPrimitive_hasDerivAt ha.continuous t).differentiableAt,?_⟩
  have he : deriv (periodicPrimitive a) = a := funext fun t =>
    (periodicPrimitive_hasDerivAt ha.continuous t).deriv
  rw [he]
  exact ha

theorem periodicPrimitive_periodic {a : ℝ → ℝ} (ha : Continuous a)
    (hp : Periodic a (2*Real.pi)) (hz : (∫ s in -Real.pi..Real.pi, a s) = 0) :
    Periodic (periodicPrimitive a) (2*Real.pi) := by
  intro t
  unfold periodicPrimitive
  rw [hp.intervalIntegral_add_eq_add _ _ (fun s t => ha.intervalIntegrable s t)]
  convert add_zero (∫ s in -Real.pi..t, a s) using 1
  congr 1
  convert hz using 1
  congr 1
  ring

theorem periodic_arg_neg {h : ℝ → ℝ} (hp : Periodic h (2*Real.pi)) {z : ℂ}
    (hz : z ≠ 0) : h z.arg = h ((-z).arg+Real.pi) := by
  by_cases hi : 0 < z.im ∨ z.im = 0 ∧ z.re < 0
  · rw [Complex.arg_neg_eq_arg_sub_pi_iff.mpr hi,sub_add_cancel]
  · have hj : z.im < 0 ∨ z.im = 0 ∧ 0 < z.re := by
      by_cases him : z.im = 0
      · right
        refine ⟨him,?_⟩
        have hn : z.re ≠ 0 := fun hn => hz (Complex.ext hn him)
        rcases lt_or_gt_of_ne hn with hn | hn
        · exact False.elim (hi (Or.inr ⟨him,hn⟩))
        · exact hn
      · exact Or.inl (lt_of_le_of_ne (le_of_not_gt (fun h => hi (Or.inl h))) him)
    rw [Complex.arg_neg_eq_arg_add_pi_iff.mpr hj]
    convert (hp z.arg).symm using 1
    congr 1
    ring

theorem contDiffAt_arg_slit {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ Complex.arg z := by
  have h := (Complex.contDiffAt_log (n := ∞) hz).restrict_scalars ℝ
  have ht : ContDiffAt ℝ ∞ (fun x : ℂ => (Complex.log x).im) z :=
    Complex.imCLM.contDiff.contDiffAt.comp z h
  simpa only [Complex.log_im] using ht

theorem periodic_arg_smooth {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hp : Periodic h (2*Real.pi)) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : ℂ => h z.arg) z := by
  by_cases hs : z ∈ Complex.slitPlane
  · exact hh.contDiffAt.comp z (contDiffAt_arg_slit hs)
  · have hsneg : -z ∈ Complex.slitPlane :=
      (Complex.mem_slitPlane_or_neg_mem_slitPlane hz).resolve_left hs
    have hd : ContDiffAt ℝ ∞ (fun w : ℂ => h ((-w).arg+Real.pi)) z :=
      hh.contDiffAt.comp z (((contDiffAt_arg_slit hsneg).comp z contDiff_neg.contDiffAt).add contDiffAt_const)
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
    exact periodic_arg_neg hp hw

theorem periodic_arg_polar {h : ℝ → ℝ} (hp : Periodic h (2*Real.pi))
    {R : ℝ} (hR : 0 < R) (t : ℝ) :
    h (Complex.arg (R*(Real.cos t+Real.sin t*Complex.I))) = h t := by
  have he := Complex.arg_mul_cos_add_sin_mul_I_sub hR t
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin] at he
  have he' : Complex.arg (R*(Real.cos t+Real.sin t*Complex.I)) =
      t + (⌊(Real.pi-t)/(2*Real.pi)⌋ : ℤ) • (2*Real.pi) := by
    rw [zsmul_eq_mul]
    linarith
  rw [he']
  exact hp.zsmul _ t

def radiusSq (p : Plane) : ℝ := p.1^2+p.2^2
@[fun_prop] theorem radiusSq_smooth : ContDiff ℝ ∞ radiusSq := by unfold radiusSq; fun_prop

@[simp] theorem radiusSq_polar (R t : ℝ) : radiusSq (polarCoord.symm (R,t)) = R^2 := by
  simp only [radiusSq,polarCoord_symm_apply]
  linear_combination R^2 * Real.cos_sq_add_sin_sq t

def angularExtension (R delta : ℝ) (hd : 0 < delta) (h : ℝ → ℝ) (p : Plane) : ℝ :=
  let b : ContDiffBump (R^2) := ⟨delta/2,delta,by positivity,by linarith⟩
  b (radiusSq p) * h (Complex.arg (Complex.equivRealProdCLM.symm p))

theorem angularExtension_zero {R delta : ℝ} (hd : 0 < delta) (h : ℝ → ℝ) (p : Plane)
    (hp : delta ≤ |radiusSq p-R^2|) : angularExtension R delta hd h p = 0 := by
  let b : ContDiffBump (R^2) := ⟨delta/2,delta,by positivity,by linarith⟩
  change b (radiusSq p) * h (Complex.arg (Complex.equivRealProdCLM.symm p)) = 0
  have hb : b (radiusSq p) = 0 := b.zero_of_le_dist (by simpa only [Real.dist_eq] using hp)
  rw [hb,zero_mul]

theorem angularExtension_smooth {R delta : ℝ} (hd : 0 < delta) (hdR : delta < R^2)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hp : Periodic h (2*Real.pi)) :
    ContDiff ℝ ∞ (angularExtension R delta hd h) := by
  let b : ContDiffBump (R^2) := ⟨delta/2,delta,by positivity,by linarith⟩
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases h0 : p = 0
  · subst p
    have hn : ∀ᶠ p : Plane in 𝓝 0, delta < |radiusSq p-R^2| := by
      apply (isOpen_lt continuous_const ((radiusSq_smooth.continuous.sub continuous_const).abs)).mem_nhds
      simpa [radiusSq,abs_of_nonneg (sq_nonneg R)] using hdR
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hn] with p hp
    exact angularExtension_zero hd h p hp.le
  · have hz : Complex.equivRealProdCLM.symm p ≠ 0 := by
      intro he
      apply h0
      apply Complex.equivRealProdCLM.symm.injective
      simpa only [map_zero] using he
    exact (b.contDiff.comp radiusSq_smooth).contDiffAt.mul
      ((periodic_arg_smooth hh hp hz).comp p Complex.equivRealProdCLM.symm.contDiff.contDiffAt)

theorem angularExtension_compact {R delta : ℝ} (hd : 0 < delta) (h : ℝ → ℝ) :
    HasCompactSupport (angularExtension R delta hd h) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Plane) (R^2+delta+1))
  intro p hp
  apply angularExtension_zero hd h p
  by_contra! ht
  have hq : radiusSq p < R^2+delta := by linarith [(abs_lt.mp ht).2]
  apply hp
  rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff,Real.norm_eq_abs,Real.norm_eq_abs]
  have h1 : p.1^2 ≤ radiusSq p := by dsimp [radiusSq]; nlinarith [sq_nonneg p.2]
  have h2 : p.2^2 ≤ radiusSq p := by dsimp [radiusSq]; nlinarith [sq_nonneg p.1]
  have hb : 0 < R^2+delta := by positivity
  constructor
  · nlinarith [sq_abs p.1,abs_nonneg p.1,sq_nonneg (|p.1|-1)]
  · nlinarith [sq_abs p.2,abs_nonneg p.2,sq_nonneg (|p.2|-1)]

theorem angularExtension_polar {R delta : ℝ} (hR : 0 < R) (hd : 0 < delta)
    {h : ℝ → ℝ} (hp : Periodic h (2*Real.pi)) (t : ℝ) :
    angularExtension R delta hd h (polarCoord.symm (R,t)) = h t := by
  let b : ContDiffBump (R^2) := ⟨delta/2,delta,by positivity,by linarith⟩
  change b (radiusSq (polarCoord.symm (R,t))) * _ = h t
  have hb : b (R^2) = 1 := b.one_of_mem_closedBall (by simp only [Metric.mem_closedBall,dist_self]; exact le_of_lt b.rIn_pos)
  rw [radiusSq_polar,hb,one_mul]
  have he : Complex.equivRealProdCLM.symm (polarCoord.symm (R,t)) =
      R*(Real.cos t+Real.sin t*Complex.I) := by
    apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply,polarCoord_symm_apply]
  rw [he]
  exact periodic_arg_polar hp hR t

end PackingSufficiencySupport.Hamiltonian
end

end OAI
