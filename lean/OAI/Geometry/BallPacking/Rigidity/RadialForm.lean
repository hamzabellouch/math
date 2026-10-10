import Mathlib
import OAI.Geometry.BallPacking.Rigidity.Adapted

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem stdDot_standardForm_sq_le {n : ℕ} (z v : Phase n) :
    (stdDot n z v)^2 + (standardForm z v)^2 ≤ stdDot n z z * stdDot n v v := by
  let z' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 z
  let v' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v
  have hr : (inner ℂ z' v').re = stdDot n z v := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.re_sum, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add, stdDot_apply]
    apply Finset.sum_congr rfl
    intro i _
    change (v i).re * (z i).re + (v i).im * (z i).im = _
    ring
  have hi : (inner ℂ z' v').im = standardForm z v := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.im_sum, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, standardForm]
    apply Finset.sum_congr rfl
    intro i _
    change (v i).re * (-(z i).im) + (v i).im * (z i).re = _
    ring
  have hz : ‖z'‖^2 = stdDot n z z := by
    simp only [EuclideanSpace.norm_sq_eq, stdDot_apply, ←Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    rfl
  have hv : ‖v'‖^2 = stdDot n v v := by
    simp only [EuclideanSpace.norm_sq_eq, stdDot_apply, ←Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    rfl
  have hh := (sq_le_sq₀ (norm_nonneg (inner ℂ z' v'))
    (mul_nonneg (norm_nonneg z') (norm_nonneg v'))).mpr (norm_inner_le_norm z' v')
  rw [←Complex.normSq_eq_norm_sq, Complex.normSq_apply, hr, hi, mul_pow, hz, hv] at hh
  nlinarith only [hh]

@[simp] theorem stdDot_J_right {n : ℕ} (v w : Phase n) :
    stdDot n v (standardJ n w) = -standardForm v w := by
  rw [←standardForm_J_right,standardJ_sq,standardForm_neg_right]

@[simp] theorem capacity_eq_stdDot {n : ℕ} (x : Phase n) :
    capacity x = Real.pi * stdDot n x x := by
  rw [←standardForm_J_right,standardForm_J_self]
  rfl

def radialSlope (σ τ t : ℝ) : ℝ :=
  -radialSwitch σ τ t / (1 + radialOffset σ τ t)^2

theorem radialSlope_nonpos (σ τ t : ℝ) : radialSlope σ τ t ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (radialSwitch_nonneg σ τ t)) (sq_nonneg _)

theorem radialSlope_zero {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    radialSlope σ τ t = 0 := by simp [radialSlope, radialSwitch_zero hστ ht]

theorem radialMoment_derivative_eq {σ τ : ℝ} (hστ : σ < τ) (t : ℝ) :
    radialCoefficient σ τ t + t * radialSlope σ τ t =
      (1 + radialOffset σ τ t - t * radialSwitch σ τ t) / (1 + radialOffset σ τ t)^2 := by
  have hn : 1 + radialOffset σ τ t ≠ 0 :=
    ne_of_gt (by linarith [radialOffset_nonneg hστ t])
  unfold radialCoefficient radialSlope
  field_simp
  ring

def radialForm {n : ℕ} (σ τ : ℝ) (x v w : Phase n) : ℝ :=
  radialCoefficient σ τ (capacity x) * standardForm v w +
    Real.pi * radialSlope σ τ (capacity x) *
      (stdDot n x v * standardForm x w - stdDot n x w * standardForm x v)

theorem radialForm_standard {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) {x : Phase n}
    (hx : capacity x ≤ σ) (v w : Phase n) :
    radialForm σ τ x v w = standardForm v w := by
  simp only [radialForm, radialCoefficient_one hστ hx,radialSlope_zero hστ hx,
    one_mul,mul_zero,zero_mul,add_zero]

theorem radialForm_J_pos {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) (hτ : τ < 1)
    (x : Phase n) {v : Phase n} (hv : v ≠ 0) :
    0 < radialForm σ τ x v (standardJ n v) := by
  have hcs := stdDot_standardForm_sq_le x v
  have hs : Real.pi * radialSlope σ τ (capacity x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (radialSlope_nonpos _ _ _)
  have hm := mul_le_mul_of_nonpos_left hcs hs
  have hp := mul_pos (radialMoment_derivative_pos hστ hτ (capacity x)) (stdDot_pos hv)
  rw [←radialMoment_derivative_eq hστ] at hp
  simp only [radialForm, standardForm_J_right, stdDot_J_right]
  rw [capacity_eq_stdDot] at hp hm ⊢
  nlinarith only [hm,hp]

theorem radialForm_adapted_pos {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) (hτ : τ < 1)
    {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    (houtside : ∀ x, σ < capacity x → J x = standardJ n) (x : Phase n)
    {v : Phase n} (hv : v ≠ 0) : 0 < radialForm σ τ x v (J x v) := by
  by_cases hx : capacity x ≤ σ
  · rw [radialForm_standard hστ hx]
    exact (hJ x).2.2 v hv
  · rw [houtside x (lt_of_not_ge hx)]
    exact radialForm_J_pos hστ hτ x hv

def stdOmega (n : ℕ) : Phase n →L[ℝ] Phase n →L[ℝ] ℝ :=
  -((stdDot n).flip.comp (standardJ n)).flip

@[simp] theorem stdOmega_apply {n : ℕ} (v w : Phase n) :
    stdOmega n v w = standardForm v w := by
  change -(stdDot n v (standardJ n w)) = standardForm v w
  rw [stdDot_J_right,neg_neg]

theorem capacity_smooth (n : ℕ) : ContDiff ℝ ∞ (@capacity n) := by
  have hd : ContDiff ℝ ∞ (fun x : Phase n => stdDot n x x) :=
    ((stdDot n).contDiff.comp contDiff_id).clm_apply contDiff_id
  have he : (@capacity n) = fun y => Real.pi * stdDot n y y := funext capacity_eq_stdDot
  rw [he]
  exact contDiff_const.mul hd

theorem capacity_hasFDerivAt {n : ℕ} (x : Phase n) :
    HasFDerivAt capacity ((2 * Real.pi) • stdDot n x) x := by
  have hd := ((stdDot n).hasFDerivAt).clm_apply (hasFDerivAt_id x)
  have hh := hd.const_mul Real.pi
  have he : Real.pi • ((stdDot n x).comp (ContinuousLinearMap.id ℝ (Phase n)) +
      (stdDot n).flip x) = (2 * Real.pi) • stdDot n x := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    rw [stdDot_symm v x]
    ring
  simp only [id_eq] at hh
  rw [he] at hh
  have hefunc : (@capacity n) = fun y => Real.pi * stdDot n y y := funext capacity_eq_stdDot
  rw [hefunc]
  exact hh

def radialPrimitiveCLM {n : ℕ} (σ τ : ℝ) (x : Phase n) : Phase n →L[ℝ] ℝ :=
  (radialCoefficient σ τ (capacity x) / 2) • stdOmega n x

theorem radialPrimitiveCLM_smooth {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) :
    ContDiff ℝ ∞ (@radialPrimitiveCLM n σ τ) :=
  (((radialCoefficient_smooth hστ).comp (capacity_smooth n)).div_const 2).smul
    (stdOmega n).contDiff

theorem radialPrimitiveCLM_derivative {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    (x v w : Phase n) :
    fderiv ℝ (radialPrimitiveCLM σ τ) x v w =
      (radialCoefficient σ τ (capacity x) / 2) * standardForm v w +
      Real.pi * radialSlope σ τ (capacity x) * stdDot n x v * standardForm x w := by
  have hg : HasFDerivAt (fun y : Phase n => radialCoefficient σ τ (capacity y) / 2)
      ((radialSlope σ τ (capacity x) / 2) • ((2 * Real.pi) • stdDot n x)) x := by
    have hc := ((radialCoefficient_hasDerivAt hστ (capacity x)).div_const 2).comp_hasFDerivAt x
      (capacity_hasFDerivAt x)
    exact hc
  have hd := hg.smul (stdOmega n).hasFDerivAt
  change HasFDerivAt (radialPrimitiveCLM σ τ) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, stdOmega_apply]
  ring

def radialPrimitive {n : ℕ} (σ τ : ℝ) (x : Phase n) : Phase n [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ (Phase n) ℝ 0 (radialPrimitiveCLM σ τ x)

theorem radialPrimitive_smooth {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) :
    ContDiff ℝ ∞ (@radialPrimitive n σ τ) := by
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Phase n) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp (radialPrimitiveCLM_smooth hστ)

theorem radialForm_extDeriv {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) (x v w : Phase n) :
    extDeriv (radialPrimitive σ τ) x ![v,w] = radialForm σ τ x v w := by
  rw [extDeriv_apply ((radialPrimitive_smooth hστ).differentiable (by simp) x)]
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change fderiv ℝ (fun y => radialPrimitiveCLM σ τ y w) x v -
    fderiv ℝ (fun y => radialPrimitiveCLM σ τ y v) x w = _
  have he (a b : Phase n) :
      fderiv ℝ (fun y => radialPrimitiveCLM σ τ y a) x b =
        fderiv ℝ (radialPrimitiveCLM σ τ) x b a := by
    rw [fderiv_clm_apply ((radialPrimitiveCLM_smooth hστ).differentiable (by simp) x)
      (differentiableAt_const a)]
    simp
  rw [he w v,he v w]
  rw [radialPrimitiveCLM_derivative hστ, radialPrimitiveCLM_derivative hστ,
    standardForm_skew w v]
  unfold radialForm
  ring

theorem radialForm_closed {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) :
    extDeriv (extDeriv (@radialPrimitive n σ τ)) = 0 :=
  extDeriv_extDeriv (radialPrimitive_smooth hστ) (by
    norm_num [minSmoothness])

theorem linear_asymptotic_norm_tendsto {n : ℕ} {u : ℂ → Phase n} {v : Phase n}
    (hv : v ≠ 0) (hlim : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v)) :
    Tendsto (fun z => ‖u z‖) (cocompact ℂ) atTop := by
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hev : ∀ᶠ z : ℂ in cocompact ℂ, ‖v‖ / 2 < ‖z⁻¹ • u z‖ :=
    (tendsto_order.mp hlim.norm).1 _ (by linarith)
  have hb : (fun z : ℂ => (‖v‖ / 2) * ‖z‖) ≤ᶠ[cocompact ℂ] fun z => ‖u z‖ := by
    filter_upwards [hev,(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz hz0
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr (by simpa using hz0)
    rw [norm_smul,norm_inv,inv_mul_eq_div] at hz
    exact ((lt_div_iff₀ hn).mp hz).le
  exact tendsto_atTop_mono' _ hb
    (Tendsto.const_mul_atTop (by linarith : 0 < ‖v‖ / 2) tendsto_norm_cocompact_atTop)

theorem AffineLineCurve.tendsto_cocompact {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) :
    Tendsto u (cocompact ℂ) (cocompact (Phase n)) := by
  obtain ⟨v,hv,hlim⟩ := hu.2.2.2.2
  rw [←Metric.cobounded_eq_cocompact (α := Phase n),←tendsto_norm_atTop_iff_cobounded]
  exact linear_asymptotic_norm_tendsto hv hlim

theorem AffineLineCurve.isProperMap {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) : IsProperMap u :=
  isProperMap_iff_tendsto_cocompact.mpr ⟨hu.1.continuous,hu.tendsto_cocompact⟩

theorem AffineLineCurve.holomorphic_at_infinity {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x - standardJ n)) :
    ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ u z := by
  filter_upwards [hu.tendsto_cocompact.eventually hJc.compl_mem_cocompact] with z hz
  have hJ : J (u z) = standardJ n :=
    sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun x => J x - standardJ n) hz)
  apply complex_differentiable_of_CR (hu.2.1 z).1
  intro w
  rw [(hu.2.1 z).2,hJ]

def infinityGerm {n : ℕ} (u : ℂ → Phase n) (v : Phase n) (w : ℂ) : Phase n :=
  if w = 0 then v else w • u w⁻¹

theorem infinityGerm_eventuallyEq {n : ℕ} (u : ℂ → Phase n) (v : Phase n)
    {w : ℂ} (hw : w ≠ 0) :
    infinityGerm u v =ᶠ[𝓝 w] fun z => z • u z⁻¹ := by
  filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hw] with z hz
  exact ite_eq_right hz

theorem infinityGerm_analyticAt {n : ℕ} {u : ℂ → Phase n} {v : Phase n}
    (hholo : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ u z)
    (hlim : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v)) :
    AnalyticAt ℂ (infinityGerm u v) 0 := by
  have hi : Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_nhdsNE_zero
  have ht : Tendsto (fun w : ℂ => w • u w⁻¹) (𝓝[≠] 0) (𝓝 v) := by
    simpa only [Function.comp_def,inv_inv] using hlim.comp hi
  have he : infinityGerm u v = Function.update (fun w : ℂ => w • u w⁻¹) 0 v := by
    classical
    funext w
    by_cases hw : w = 0
    · subst w; simp [infinityGerm]
    · simp [infinityGerm,hw]
  have hc : ContinuousAt (infinityGerm u v) 0 := by
    classical
    rw [he,continuousAt_update_same]
    exact ht
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hc
  filter_upwards [hi.eventually hholo,self_mem_nhdsWithin] with w hw hw0
  have hn : w ≠ 0 := hw0
  have hd : DifferentiableAt ℂ (fun z : ℂ => z • u z⁻¹) w :=
    differentiableAt_id.smul (hw.comp w (differentiableAt_id.inv hn))
  exact hd.congr_of_eventuallyEq (infinityGerm_eventuallyEq u v hn)

theorem AffineLineCurve.analytic_at_infinity {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x - standardJ n)) :
    ∃ v : Phase n, v ≠ 0 ∧ AnalyticAt ℂ (infinityGerm u v) 0 ∧
      infinityGerm u v 0 = v := by
  obtain ⟨v,hv,hlim⟩ := hu.2.2.2.2
  exact ⟨v,hv,infinityGerm_analyticAt (hu.holomorphic_at_infinity hJc) hlim,by simp [infinityGerm]⟩

end HigherDimensionalBallPacking.Rigidity

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

abbrev Plane := ℝ × ℝ

def planarArea : Plane →L[ℝ] Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.fst ℝ ℝ ℝ)
    (ContinuousLinearMap.snd ℝ ℝ ℝ) -
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (ContinuousLinearMap.fst ℝ ℝ ℝ)

@[simp] theorem planarArea_apply (v w : Plane) : planarArea v w = v.1*w.2-v.2*w.1 := rfl
def planarCurl (alpha : Plane → Plane →L[ℝ] ℝ) (p : Plane) : ℝ :=
  fderiv ℝ alpha p (1,0) (0,1) - fderiv ℝ alpha p (0,1) (1,0)
def radiusSq (p : Plane) : ℝ := p.1^2+p.2^2
@[simp] theorem radiusSq_nonneg (p : Plane) : 0 ≤ radiusSq p :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

@[fun_prop] theorem radiusSq_smooth : ContDiff ℝ ∞ radiusSq := by unfold radiusSq; fun_prop

@[simp] theorem radiusSq_polar (R t : ℝ) : radiusSq (polarCoord.symm (R,t)) = R^2 := by
  simp only [radiusSq,polarCoord_symm_apply]
  linear_combination R^2 * Real.cos_sq_add_sin_sq t

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

theorem radialArea_curl {f : ℝ → ℝ} {point : Plane}
    (hf : DifferentiableAt ℝ f (radiusSq point)) :
    planarCurl (fun p : Plane => f (radiusSq p) • planarArea p) point=
      2*(f (radiusSq point)+radiusSq point*deriv f (radiusSq point)) := by
  have H := (hf.hasDerivAt.comp_hasFDerivAt point
    (radiusSq_hasFDerivAt point)).smul planarArea.hasFDerivAt
  change HasFDerivAt (fun p : Plane => f (radiusSq p) • planarArea p) _ point at H
  unfold planarCurl
  rw [H.fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,planarArea_apply,planarDot_apply,
    Function.comp_apply]
  dsimp only [radiusSq]
  ring

theorem cutoffAngular_curl {g : ℝ → ℝ} {point : Plane}
    (hg : DifferentiableAt ℝ g (radiusSq point)) (hz : radiusSq point≠0) :
    planarCurl (fun p : Plane => g (radiusSq p) • angularOneForm p) point=
      2*deriv g (radiusSq point) := by
  have hd := hg.hasDerivAt.div (hasDerivAt_id (radiusSq point)) hz
  change HasDerivAt (fun t => g t / t) _ (radiusSq point) at hd
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

end SymplecticBallPacking.Hamiltonian
end

end OAI
