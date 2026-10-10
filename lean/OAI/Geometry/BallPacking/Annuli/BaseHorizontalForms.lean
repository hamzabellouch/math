import Mathlib
import OAI.Geometry.BallPacking.Annuli.LayerCoordinates

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold MeasureTheory
open scoped ContDiff Manifold Topology

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def firstBaseCoefficient (a : ℝ × E → ℝ) (p : Plane × E) : ℝ := a (p.1.1,p.2)

@[fun_prop] theorem firstBaseCoefficient_smooth {a : ℝ × E → ℝ}
    (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (firstBaseCoefficient a) :=
  ha.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)

theorem firstBaseCoefficient_fderiv {a : ℝ × E → ℝ}
    (ha : ContDiff ℝ ∞ a) (p v : Plane × E) :
    fderiv ℝ (firstBaseCoefficient a) p v = fderiv ℝ a (p.1.1,p.2) (v.1.1,v.2) := by
  have hh := ((ha.differentiable (by simp) (p.1.1,p.2)).hasFDerivAt.comp p
    (((hasFDerivAt_fst (𝕜 := ℝ) (p := p.1)).comp p
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))).fderiv
  exact congrArg (fun L : (Plane × E) →L[ℝ] ℝ => L v) hh

theorem firstBase_horizontalCoupling (Ω : E →L[ℝ] E →L[ℝ] ℝ)
    {a : ℝ × E → ℝ} (ha : ContDiff ℝ ∞ a) (p v w : Plane × E) :
    horizontalCoupling Ω (firstBaseCoefficient a) 0 p v w = Ω v.2 w.2 +
      fderiv ℝ a (p.1.1,p.2) (0,v.2) *w.1.1 -
      v.1.1*fderiv ℝ a (p.1.1,p.2) (0,w.2) := by
  have h0 : DifferentiableAt ℝ (0 : Plane × E → ℝ) p := differentiableAt_const 0
  rw [horizontalCoupling_eq ((firstBaseCoefficient_smooth ha).differentiable (by simp) p) h0]
  simp only [twoCovectorForm_apply,firstBaseCoefficient_fderiv ha,fderiv_zero,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply]
  change Ω v.2 w.2 + (0-fderiv ℝ a (p.1.1,p.2) 0)*(v.1.1*w.1.2-v.1.2*w.1.1)+
      0*w.1.2-v.1.2*0+fderiv ℝ a (p.1.1,p.2) (0,v.2)*w.1.1-
      v.1.1*fderiv ℝ a (p.1.1,p.2) (0,w.2) = _
  simp

theorem secondBase_horizontalCoupling_isInvertible [FiniteDimensional ℝ E]
    {Ω : E →L[ℝ] E →L[ℝ] ℝ} (hΩ : Ω.IsInvertible)
    {b : ℝ × E → ℝ} (hb : ContDiff ℝ ∞ b) (p : Plane × E)
    (hpositive : 0 < fderiv ℝ b (p.1.1,p.2) (1,0)) :
    (horizontalCoupling Ω 0 (firstBaseCoefficient b) p).IsInvertible := by
  have h0 : DifferentiableAt ℝ (0 : Plane × E → ℝ) p := differentiableAt_const 0
  rw [horizontalCoupling_eq h0 ((firstBaseCoefficient_smooth hb).differentiable (by simp) p)]
  simp only [fderiv_zero,Pi.zero_apply,zero_apply,sub_zero,firstBaseCoefficient_fderiv hb,
    ContinuousLinearMap.zero_comp]
  have he : twoCovectorForm Ω (fderiv ℝ b (p.1.1,p.2) (1,0)) 0
      ((fderiv ℝ (firstBaseCoefficient b) p).comp (ContinuousLinearMap.inr ℝ Plane E)) =
      oneCovectorForm Ω (fderiv ℝ b (p.1.1,p.2) (1,0))
        ((fderiv ℝ (firstBaseCoefficient b) p).comp (ContinuousLinearMap.inr ℝ Plane E)) := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp only [twoCovectorForm_apply,oneCovectorForm_apply,zero_apply,zero_mul,mul_zero,add_zero,sub_zero]
  rw [he]
  exact oneCovectorForm_isInvertible hΩ (ne_of_gt hpositive) _

theorem horizontalCoupling_oneCovector_isInvertible [FiniteDimensional ℝ E]
    {Ω : E →L[ℝ] E →L[ℝ] ℝ} (hΩ : Ω.IsInvertible)
    {A B : Plane × E → ℝ} {p : Plane × E}
    (hA : DifferentiableAt ℝ A p) (hB : DifferentiableAt ℝ B p)
    (hvertical : (fderiv ℝ A p).comp (ContinuousLinearMap.inr ℝ Plane E)=0)
    (hpositive : 0<fderiv ℝ B p ((1,0),0)-fderiv ℝ A p ((0,1),0)) :
    (horizontalCoupling Ω A B p).IsInvertible := by
  rw [horizontalCoupling_eq hA hB,hvertical]
  have he (c : ℝ) (η : E →L[ℝ] ℝ) : twoCovectorForm Ω c 0 η=oneCovectorForm Ω c η := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp only [twoCovectorForm_apply,oneCovectorForm_apply,zero_apply,zero_mul,mul_zero,add_zero,sub_zero]
  rw [he]
  exact oneCovectorForm_isInvertible hΩ (ne_of_gt hpositive) _

def baseCoefficient (a : Plane → ℝ) (p : Plane × E) : ℝ := a p.1

@[fun_prop] theorem baseCoefficient_smooth {a : Plane → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (baseCoefficient (E := E) a) := ha.comp contDiff_fst

theorem baseCoefficient_fderiv {a : Plane → ℝ} (ha : ContDiff ℝ ∞ a) (p v : Plane × E) :
    fderiv ℝ (baseCoefficient a) p v=fderiv ℝ a p.1 v.1 := by
  exact congrArg (fun L : (Plane × E) →L[ℝ] ℝ => L v)
    (((ha.differentiable (by simp) p.1).hasFDerivAt.comp p
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).fderiv)

theorem baseCoefficient_vertical {a : Plane → ℝ} (ha : ContDiff ℝ ∞ a) (p : Plane × E) :
    (fderiv ℝ (baseCoefficient a) p).comp (ContinuousLinearMap.inr ℝ Plane E)=0 := by
  apply ContinuousLinearMap.ext
  intro z
  change fderiv ℝ (baseCoefficient a) p (0,z)=0
  rw [baseCoefficient_fderiv ha]
  exact map_zero _

def weightedSecondCoefficient (b w : Plane → ℝ) (G : ℝ × E → ℝ) (p : Plane × E) : ℝ :=
  b p.1+w p.1*G (p.1.1,p.2)

@[fun_prop] theorem weightedSecondCoefficient_smooth {b w : Plane → ℝ} {G : ℝ × E → ℝ}
    (hb : ContDiff ℝ ∞ b) (hw : ContDiff ℝ ∞ w) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (weightedSecondCoefficient b w G) :=
  (baseCoefficient_smooth hb).add ((baseCoefficient_smooth hw).mul (firstBaseCoefficient_smooth hG))

theorem weightedSecondCoefficient_fderiv {b w : Plane → ℝ} {G : ℝ × E → ℝ}
    (hb : ContDiff ℝ ∞ b) (hw : ContDiff ℝ ∞ w) (hG : ContDiff ℝ ∞ G) (p v : Plane × E) :
    fderiv ℝ (weightedSecondCoefficient b w G) p v =
      fderiv ℝ b p.1 v.1+fderiv ℝ w p.1 v.1*G (p.1.1,p.2)+
        w p.1*fderiv ℝ G (p.1.1,p.2) (v.1.1,v.2) := by
  have hbD := (baseCoefficient_smooth (E := E) hb).differentiable (by simp) p
  have hwD := (baseCoefficient_smooth (E := E) hw).differentiable (by simp) p
  have hgD := (firstBaseCoefficient_smooth hG).differentiable (by simp) p
  change fderiv ℝ (baseCoefficient b+baseCoefficient w*firstBaseCoefficient G) p v = _
  rw [fderiv_add hbD (hwD.mul hgD),fderiv_mul hwD hgD]
  simp only [add_apply,smul_apply,smul_eq_mul,baseCoefficient_fderiv hb,baseCoefficient_fderiv hw,
    firstBaseCoefficient_fderiv hG,baseCoefficient,firstBaseCoefficient]
  ring

theorem weighted_horizontalCoupling_isInvertible [FiniteDimensional ℝ E]
    {Ω : E →L[ℝ] E →L[ℝ] ℝ} (hΩ : Ω.IsInvertible)
    {a b w : Plane → ℝ} {G : ℝ × E → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hw : ContDiff ℝ ∞ w)
    (hG : ContDiff ℝ ∞ G) (p : Plane × E)
    (hbase : 0<fderiv ℝ b p.1 (1,0)-fderiv ℝ a p.1 (0,1))
    (hwzero : fderiv ℝ w p.1 (1,0)=0) (hwpos : 0≤w p.1)
    (hGpos : 0≤fderiv ℝ G (p.1.1,p.2) (1,0)) :
    (horizontalCoupling Ω (baseCoefficient a) (weightedSecondCoefficient b w G) p).IsInvertible := by
  apply horizontalCoupling_oneCovector_isInvertible hΩ
    ((baseCoefficient_smooth ha).differentiable (by simp) p)
    ((weightedSecondCoefficient_smooth hb hw hG).differentiable (by simp) p)
    (baseCoefficient_vertical ha p)
  rw [weightedSecondCoefficient_fderiv hb hw hG,baseCoefficient_fderiv ha]
  dsimp only
  rw [hwzero,zero_mul,add_zero]
  linarith [mul_nonneg hwpos hGpos]

end

abbrev CircleModel := EuclideanSpace ℝ (Fin 1)

def circleInclusion (z : Circle) : ℂ := z

def ambientAngular (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (1/(2*Real.pi)) • (Complex.imCLM.comp (ContinuousLinearMap.mul ℝ ℂ (starRingEnd ℂ z)))

@[simp] theorem ambientAngular_apply (z w : ℂ) :
    ambientAngular z w = (1/(2*Real.pi))*((starRingEnd ℂ z)*w).im := rfl

theorem ambientAngular_smooth : ContDiff ℝ ∞ ambientAngular := by
  apply ContDiff.const_smul
  exact contDiff_const.clm_comp
    ((ContinuousLinearMap.mul ℝ ℂ).contDiff.comp Complex.conjCLE.contDiff)

def circleAngular : ManifoldOneForm CircleModel Circle :=
  manifoldPullbackOneForm (fun _ => ambientAngular) circleInclusion 0

theorem chartOneForm_euclidean (α : ℂ → ℂ →L[ℝ] ℝ) (c y : ℂ) :
    chartOneForm α c y=α y := by
  simp only [chartOneForm,chartDifferential,extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe,PartialEquiv.refl_symm,fderiv_id,
    mfderiv_eq_fderiv,ContinuousLinearMap.inverse_id,ContinuousLinearMap.comp_id,id_eq]

theorem ambientAngular_chart_smooth (c : ℂ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℂ => chartOneForm ambientAngular c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,ℂ) c).target) := by
  simpa only [chartOneForm_euclidean,Function.comp_def] using
    (ambientAngular_smooth.comp contDiff_snd).contDiffOn

theorem circle_coe_smooth : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℂ) ∞
    circleInclusion := by
  let := finrank_real_complex_fact'
  exact contMDiff_coe_sphere (E := ℂ) (n := 1)

theorem circleAngular_joint_smooth (c : Circle) :
    ContDiffOn ℝ ∞ (fun q : ℝ × CircleModel => chartOneForm circleAngular c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,CircleModel) c).target) := by
  exact manifoldPullbackOneForm_smooth (α := fun _ => ambientAngular)
    circle_coe_smooth ambientAngular_chart_smooth c

theorem circleAngular_smooth (c : Circle) :
    ContDiffOn ℝ ∞ (chartOneForm circleAngular c) (extChartAt 𝓘(ℝ,CircleModel) c).target := by
  exact (circleAngular_joint_smooth c).comp (f := fun y : CircleModel => ((0:ℝ),y))
    (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _,hy⟩)

theorem circleAngular_closed (z : Circle) : manifoldExteriorOneForm circleAngular z=0 := by
  let e : CircleModel := EuclideanSpace.single 0 1
  have he (v : CircleModel) : v=(v 0) • e := by
    ext i
    fin_cases i
    simp [e]
  have hz := manifoldExteriorOneForm_skew circleAngular z e e
  have hzero : manifoldExteriorOneForm circleAngular z e e=0 := by linarith
  ext v w
  rw [he v,he w]
  simp only [map_smul,smul_apply,smul_eq_mul,hzero,mul_zero,zero_apply]

def circleTurn (t : ℝ) : Circle := Circle.exp (2*Real.pi*t)

theorem circleTurn_smooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) ∞ circleTurn :=
  contMDiff_circleExp.comp ((contDiff_const.mul contDiff_id).contMDiff)

theorem circleTurn_deriv (t : ℝ) :
    HasDerivAt (fun s : ℝ => (circleTurn s : ℂ))
      ((circleTurn t : ℂ)*((2*Real.pi : ℝ):ℂ)*Complex.I) t := by
  have h := ((((hasDerivAt_id t).const_mul (2*Real.pi)).ofReal_comp).mul_const Complex.I).cexp
  simpa only [circleTurn,Circle.coe_exp,one_mul,mul_one,mul_assoc,id_eq] using h

theorem circleAngular_unit_pullback (t v : ℝ) :
    circleAngular (circleTurn t)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn t v)=v := by
  have hc := mfderiv_comp t
    ((circle_coe_smooth.mdifferentiable (by simp)) (circleTurn t))
    ((circleTurn_smooth.mdifferentiable (by simp)) t)
  simp only [circleAngular,manifoldPullbackOneForm,manifoldMapDifferential]
  change ambientAngular (circleInclusion (circleTurn t))
    (((mfderiv 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℂ) circleInclusion (circleTurn t)).comp
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn t)) v)=v
  rw [← hc,mfderiv_eq_fderiv]
  change ambientAngular (circleTurn t : ℂ)
    (fderiv ℝ (fun s : ℝ => (circleTurn s : ℂ)) t v)=v
  rw [(circleTurn_deriv t).hasFDerivAt.fderiv,ambientAngular_apply]
  have hu : starRingEnd ℂ (circleTurn t : ℂ)*(circleTurn t : ℂ)=1 := by
    rw [← Circle.coe_inv_eq_conj,← Circle.coe_mul,inv_mul_cancel,Circle.coe_one]
  have he : starRingEnd ℂ (circleTurn t : ℂ)*
      (v • ((circleTurn t : ℂ)*((2*Real.pi : ℝ):ℂ)*Complex.I)) =
      (v:ℂ)*((2*Real.pi : ℝ):ℂ)*Complex.I := by
    rw [Complex.real_smul]
    calc
      _ = (v:ℂ)*(starRingEnd ℂ (circleTurn t : ℂ)*(circleTurn t : ℂ))*
          ((2*Real.pi : ℝ):ℂ)*Complex.I := by ring
      _ = _ := by rw [hu,mul_one]
  change (1/(2*Real.pi))*(starRingEnd ℂ (circleTurn t : ℂ)*
    (v • ((circleTurn t : ℂ)*((2*Real.pi : ℝ):ℂ)*Complex.I))).im=v
  rw [he]
  simp only [Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,mul_one]
  field_simp

def shortCircleArgument (z : Circle) : ℝ := Complex.arg z/(2*Real.pi)

theorem circleTurn_isOpenMap : IsOpenMap circleTurn := by
  exact isLocalHomeomorph_circleExp.isOpenMap.comp
    (Homeomorph.mulLeft₀ (2*Real.pi) (by positivity)).isOpenMap

theorem shortCircleArgument_turn {s : ℝ} (hs : s ∈ Ioo (-(1/2):ℝ) (1/2)) :
    shortCircleArgument (circleTurn s)=s := by
  have h1 : -Real.pi<2*Real.pi*s := by
    have ht := mul_lt_mul_of_pos_left hs.1 (show 0<2*Real.pi by positivity)
    nlinarith
  have h2 : 2*Real.pi*s<Real.pi := by
    have ht := mul_lt_mul_of_pos_left hs.2 (show 0<2*Real.pi by positivity)
    nlinarith
  unfold shortCircleArgument circleTurn
  rw [Circle.arg_exp h1 h2.le]
  field_simp

theorem real_contDiffAt_argument {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ Complex.arg z := by
  have hlog : ContDiffAt ℝ ∞ Complex.log z :=
    (Complex.contDiffAt_log hz).restrict_scalars ℝ
  have ht := Complex.imCLM.contDiff.contDiffAt.comp z hlog
  change ContDiffAt ℝ ∞ (fun x => (Complex.log x).im) z at ht
  simpa only [Complex.log_im] using ht

theorem shortCircleArgument_smooth_at {z : Circle} (hz : (z : ℂ) ∈ Complex.slitPlane) :
    ContMDiffAt 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ shortCircleArgument z := by
  have ha : ContMDiffAt 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞
      (fun w : Circle => Complex.arg (circleInclusion w)) z :=
    (real_contDiffAt_argument hz).contMDiffAt.comp z circle_coe_smooth.contMDiffAt
  exact ha.div_const (2*Real.pi)

theorem circleTurn_short_slit {s : ℝ} (hs : s ∈ Ioo (-(1/2):ℝ) (1/2)) :
    (circleTurn s : ℂ) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff_arg.mpr
  refine ⟨?_,Circle.coe_ne_zero _⟩
  have h1 : -Real.pi<2*Real.pi*s := by
    have ht := mul_lt_mul_of_pos_left hs.1 (show 0<2*Real.pi by positivity)
    nlinarith
  have h2 : 2*Real.pi*s<Real.pi := by
    have ht := mul_lt_mul_of_pos_left hs.2 (show 0<2*Real.pi by positivity)
    nlinarith
  simpa only [circleTurn,Circle.arg_exp h1 h2.le] using h2.ne

def circleBandCoordinate : PartialDiffeomorph 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) ℝ Circle ∞ where
  toFun := circleTurn
  invFun := shortCircleArgument
  source := Ioo (-(1/2):ℝ) (1/2)
  target := circleTurn '' Ioo (-(1/2):ℝ) (1/2)
  map_source' s hs := ⟨s,hs,rfl⟩
  map_target' := by
    rintro z ⟨s,hs,rfl⟩
    rwa [shortCircleArgument_turn hs]
  left_inv' := fun _ hs => shortCircleArgument_turn hs
  right_inv' := by
    rintro z ⟨s,hs,rfl⟩
    rw [shortCircleArgument_turn hs]
  open_source := isOpen_Ioo
  open_target := circleTurn_isOpenMap _ isOpen_Ioo
  contMDiffOn_toFun := circleTurn_smooth.contMDiffOn
  contMDiffOn_invFun := by
    rintro z ⟨s,hs,rfl⟩
    exact (shortCircleArgument_smooth_at (circleTurn_short_slit hs)).contMDiffWithinAt

@[simp] theorem circleBandCoordinate_apply (s : ℝ) : circleBandCoordinate s=circleTurn s := rfl

@[simp] theorem circleBandCoordinate_source :
    circleBandCoordinate.source=Ioo (-(1/2):ℝ) (1/2) := rfl

theorem circleBand_compact {a b : ℝ} :
    IsCompact (circleTurn '' Icc a b) := isCompact_Icc.image circleTurn_smooth.continuous

def intervalClock (a b s : ℝ) : ℝ := Real.smoothTransition ((s-a)/(b-a))

@[fun_prop] theorem intervalClock_smooth (a b : ℝ) : ContDiff ℝ ∞ (intervalClock a b) := by
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem intervalClock_monotone {a b : ℝ} (hab : a < b) : Monotone (intervalClock a b) := by
  intro x y hxy
  exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_nonneg.mpr hab.le))

theorem intervalClock_deriv_nonneg {a b : ℝ} (hab : a < b) (s : ℝ) :
    0 ≤ deriv (intervalClock a b) s := (intervalClock_monotone hab).deriv_nonneg

theorem intervalClock_zero {a b s : ℝ} (hab : a < b) (hs : s ≤ a) : intervalClock a b s=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (sub_nonneg.mpr hab.le))

theorem intervalClock_one {a b s : ℝ} (hab : a < b) (hs : b ≤ s) : intervalClock a b s=1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hab)).2 (by linarith))

theorem intervalClock_bounds (a b s : ℝ) : 0 ≤ intervalClock a b s ∧ intervalClock a b s ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem exists_ordered_smooth_clocks (N : ℕ) {a b : ℝ} (hab : a < b) :
    ∃ lo hi : Fin N → ℝ, ∃ ρ : Fin N → ℝ → ℝ,
      (∀ i, a < lo i ∧ lo i < hi i ∧ hi i < b) ∧
      (∀ i j, i < j → hi i < lo j) ∧
      (∀ i, ContDiff ℝ ∞ (ρ i) ∧ Monotone (ρ i)) ∧
      (∀ i s, 0 ≤ ρ i s ∧ ρ i s ≤ 1 ∧ 0 ≤ deriv (ρ i) s) ∧
      (∀ i, ∃ δ : ℝ, 0 < δ ∧
        (∀ s, s ≤ lo i+δ → ρ i s=0) ∧
        (∀ s, hi i-δ ≤ s → ρ i s=1)) := by
  let D : ℝ := (b-a)/(3*(N : ℝ)+1)
  have hden : 0 < 3*(N : ℝ)+1 := by positivity
  have hD : 0 < D := div_pos (sub_pos.mpr hab) hden
  have hDeq : D*(3*(N : ℝ)+1)=b-a := by dsimp [D]; field_simp
  let lo : Fin N → ℝ := fun i => a+D*(3*(i.val : ℝ)+1)
  let hi : Fin N → ℝ := fun i => a+D*(3*(i.val : ℝ)+2)
  let ρ : Fin N → ℝ → ℝ := fun i => intervalClock (lo i+D/4) (hi i-D/4)
  have hbetween (i : Fin N) : lo i+D/4 < hi i-D/4 := by dsimp [lo,hi]; nlinarith
  refine ⟨lo,hi,ρ,?_,?_,?_,?_,?_⟩
  · intro i
    have hiN : (i.val : ℝ)+1 ≤ N := by exact_mod_cast i.isLt
    have hi0 : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    dsimp [lo,hi]
    constructor
    · nlinarith
    constructor
    · nlinarith
    · nlinarith
  · intro i j hij
    have hv : (i.val : ℝ)+1 ≤ j.val := by exact_mod_cast hij
    dsimp [lo,hi]
    nlinarith
  · intro i
    exact ⟨intervalClock_smooth _ _,intervalClock_monotone (hbetween i)⟩
  · intro i s
    exact ⟨(intervalClock_bounds _ _ _).1,(intervalClock_bounds _ _ _).2,
      intervalClock_deriv_nonneg (hbetween i) s⟩
  · intro i
    exact ⟨D/4,by positivity,fun _ hs => intervalClock_zero (hbetween i) hs,
      fun _ hs => intervalClock_one (hbetween i) hs⟩

theorem circleTurn_shortCircleArgument (z : Circle) :
    circleTurn (shortCircleArgument z)=z := by
  unfold circleTurn shortCircleArgument
  rw [mul_div_cancel₀ _ (show 2*Real.pi≠0 by positivity)]
  exact Circle.exp_arg z

theorem intervalClock_deriv_smooth (a b : ℝ) : ContDiff ℝ ∞ (deriv (intervalClock a b)) :=
  (contDiff_infty_iff_deriv.mp (intervalClock_smooth a b)).2

theorem intervalClock_deriv_zero_left {a b s : ℝ} (hab : a<b) (hs : s<a) :
    deriv (intervalClock a b) s=0 := by
  have he : intervalClock a b =ᶠ[𝓝 s] fun _ => (0:ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds hs] with t ht
    exact intervalClock_zero hab ht.le
  rw [he.deriv_eq,deriv_const]

theorem intervalClock_deriv_zero_right {a b s : ℝ} (hab : a<b) (hs : b<s) :
    deriv (intervalClock a b) s=0 := by
  have he : intervalClock a b =ᶠ[𝓝 s] fun _ => (1:ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    exact intervalClock_one hab ht.le
  rw [he.deriv_eq,deriv_const]

def circleClockDensity (b : ℝ) (z : Circle) : ℝ :=
  deriv (intervalClock (-b) b) (shortCircleArgument z)

theorem circleClockDensity_support {b : ℝ} (hb : 0<b) :
    support (circleClockDensity b) ⊆ circleTurn '' Icc (-b) b := by
  intro z hz
  refine ⟨shortCircleArgument z,?_,circleTurn_shortCircleArgument z⟩
  have hab : -b<b := by linarith
  constructor
  · by_contra hn
    exact hz (intervalClock_deriv_zero_left hab (lt_of_not_ge hn))
  · by_contra hn
    exact hz (intervalClock_deriv_zero_right hab (lt_of_not_ge hn))

theorem circleClockDensity_tsupport {b : ℝ} (hb : 0<b) :
    tsupport (circleClockDensity b) ⊆ circleTurn '' Icc (-b) b :=
  closure_minimal (circleClockDensity_support hb) circleBand_compact.isClosed

theorem circleClockDensity_smooth {b : ℝ} (hb : 0<b) (hsmall : b<1/2) :
    ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ (circleClockDensity b) := by
  intro z
  by_cases hz : z∈circleTurn '' Icc (-b) b
  · obtain ⟨s,hs,rfl⟩ := hz
    have hin : s∈Ioo (-(1/2):ℝ) (1/2) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
    exact (intervalClock_deriv_smooth (-b) b).contMDiff.contMDiffAt.comp _
      (shortCircleArgument_smooth_at (circleTurn_short_slit hin))
  · apply (contMDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [circleBand_compact.isClosed.isOpen_compl.mem_nhds hz] with w hw
    by_contra hs
    exact hw (circleClockDensity_support hb hs)

theorem circleClockDensity_nonneg {b : ℝ} (hb : 0<b) (z : Circle) :
    0≤circleClockDensity b z :=
  intervalClock_deriv_nonneg (by linarith) _

theorem circleClockDensity_turn {b s : ℝ} (hs : s∈Ioo (-(1/2):ℝ) (1/2)) :
    circleClockDensity b (circleTurn s)=deriv (intervalClock (-b) b) s := by
  unfold circleClockDensity
  rw [shortCircleArgument_turn hs]

theorem circleClockDensity_integral {b : ℝ} (hb : 0<b) (hsmall : b<1/2) :
    (∫ s in (-(1/2):ℝ)..(1/2),circleClockDensity b (circleTurn s))=1 := by
  rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (-(1/2):ℝ)≤1/2)
    (fun s hs => circleClockDensity_turn hs)]
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun s _ => (intervalClock_smooth (-b) b).differentiable (by simp) s)
    ((intervalClock_deriv_smooth (-b) b).continuous.intervalIntegrable _ _)]
  rw [intervalClock_one (by linarith : -b<b) hsmall.le,
    intervalClock_zero (by linarith : -b<b) (by linarith)]
  norm_num

 theorem expNegInvGlue_hasDerivAt (x : ℝ) :
    HasDerivAt expNegInvGlue (x⁻¹^2*expNegInvGlue x) x := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) x

 theorem smoothTransition_deriv_pos {x : ℝ} (hx : x∈Ioo (0:ℝ) 1) :
    0<deriv Real.smoothTransition x := by
  have hA := expNegInvGlue_hasDerivAt x
  have hB := (expNegInvGlue_hasDerivAt (1-x)).comp x ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))
  have hd := hA.div (hA.add hB) (ne_of_gt (Real.smoothTransition.pos_denom x))
  change HasDerivAt Real.smoothTransition _ x at hd
  rw [hd.deriv]
  have h₁ := expNegInvGlue.pos_of_pos hx.1
  have h₂ := expNegInvGlue.pos_of_pos (sub_pos.mpr hx.2)
  apply div_pos _ (sq_pos_of_pos (Real.smoothTransition.pos_denom x))
  have h₃ : 0<x⁻¹^2 := sq_pos_of_pos (inv_pos.mpr hx.1)
  have h₄ : 0<(1-x)⁻¹^2 := sq_pos_of_pos (inv_pos.mpr (sub_pos.mpr hx.2))
  have he : x⁻¹^2*expNegInvGlue x*(expNegInvGlue x+expNegInvGlue (1-x))-
      expNegInvGlue x*(x⁻¹^2*expNegInvGlue x+((1-x)⁻¹^2*expNegInvGlue (1-x))*(0-1))=
      expNegInvGlue x*expNegInvGlue (1-x)*(x⁻¹^2+(1-x)⁻¹^2) := by ring
  dsimp only [Pi.add_apply,Function.comp_apply]
  rw [he]
  positivity

 theorem intervalClock_deriv_pos {a b s : ℝ} (hab : a<b) (hs : s∈Ioo a b) :
    0<deriv (intervalClock a b) s := by
  have hx : (s-a)/(b-a)∈Ioo (0:ℝ) 1 := by
    constructor
    · exact div_pos (sub_pos.mpr hs.1) (sub_pos.mpr hab)
    · exact (div_lt_one (sub_pos.mpr hab)).mpr (by linarith [hs.2])
  have htr : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hd := (htr.differentiable (by simp) ((s-a)/(b-a))).hasDerivAt.comp s
    (((hasDerivAt_id s).sub_const a).div_const (b-a))
  change HasDerivAt (intervalClock a b) _ s at hd
  rw [hd.deriv]
  exact mul_pos (smoothTransition_deriv_pos hx) (div_pos zero_lt_one (sub_pos.mpr hab))

 theorem intervalClock_strictMonoOn {a b : ℝ} (hab : a<b) :
    StrictMonoOn (intervalClock a b) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (intervalClock_smooth a b).continuous.continuousOn
  simpa only [interior_Icc] using (fun s hs => intervalClock_deriv_pos hab (s := s) hs)

 theorem intervalClock_image {a b : ℝ} (hab : a<b) :
    intervalClock a b '' Ioo a b=Ioo (0:ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨s,hs,rfl⟩
    have hm := intervalClock_strictMonoOn hab
    constructor
    · simpa only [intervalClock_zero hab le_rfl] using hm ⟨le_rfl,hab.le⟩ ⟨hs.1.le,hs.2.le⟩ hs.1
    · simpa only [intervalClock_one hab le_rfl] using hm ⟨hs.1.le,hs.2.le⟩ ⟨hab.le,le_rfl⟩ hs.2
  · intro T hT
    apply intermediate_value_Ioo hab.le (intervalClock_smooth a b).continuous.continuousOn
    simpa only [intervalClock_zero hab le_rfl,intervalClock_one hab le_rfl] using hT

 theorem intervalClock_smooth_inverse {a b : ℝ} (hab : a<b) :
    ∃ g : ℝ → ℝ,ContDiffOn ℝ ∞ g (Ioo (0:ℝ) 1) ∧
      (∀ s∈Ioo a b,g (intervalClock a b s)=s) ∧
      (∀ T∈Ioo (0:ℝ) 1,g T∈Ioo a b ∧ intervalClock a b (g T)=T) := by
  have hm : InjOn (intervalClock a b) (Ioo a b) :=
    (intervalClock_strictMonoOn hab).injOn.mono Ioo_subset_Icc_self
  have hi (s : ℝ) (hs : s∈Ioo a b) : (fderiv ℝ (intervalClock a b) s).IsInvertible := by
    let c := deriv (intervalClock a b) s
    let e : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ c (ne_of_gt (intervalClock_deriv_pos hab hs))).toContinuousLinearEquiv
    refine ⟨e,?_⟩
    ext
    simp [e,c]
  obtain ⟨_,hsm,hl,hr⟩ := smooth_inverse_on isOpen_Ioo (intervalClock_smooth a b).contDiffOn hm hi
  rw [intervalClock_image hab] at hsm hr
  refine ⟨invFunOn (intervalClock a b) (Ioo a b),hsm,hl,?_⟩
  intro T hT
  exact ⟨invFunOn_mem (show T∈intervalClock a b '' Ioo a b from (intervalClock_image hab).symm ▸ hT),hr T hT⟩

 theorem circleClockDensity_pos {b s : ℝ} (hb : 0<b) (hsmall : b<1/2) (hs : s∈Ioo (-b) b) :
    0<circleClockDensity b (circleTurn s) := by
  rw [circleClockDensity_turn (show s∈Ioo (-(1/2):ℝ) (1/2) from ⟨by linarith [hs.1],by linarith [hs.2]⟩)]
  exact intervalClock_deriv_pos (by linarith) hs

end PackingSufficiencySupport.Hamiltonian
end

end OAI
