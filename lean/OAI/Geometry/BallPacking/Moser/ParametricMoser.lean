import Mathlib
import OAI.Geometry.BallPacking.Moser.ManifoldMoserField

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Function MeasureTheory
section
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parametric_relative_primitive {ι : Type*} [Fintype ι]
    {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hf0 : ∀ y, (∫ p, f (y,p)) = 0)
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) (hRi : Injective R)
    (hz : ∀ i y, (∫ p in roundDisk (R i), f (y,p)) = 0) :
    ∃ U V : P × Plane → ℝ, ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ V ∧
      HasCompactSupport U ∧ HasCompactSupport V ∧
      (∀ y p, deriv (fun x => V (y,(x,p.2))) p.1 -
        deriv (fun t => U (y,(p.1,t))) p.2 = f (y,p)) ∧
      (∀ i y p, radiusSq p = (R i)^2 → -p.2*U (y,p)+p.1*V (y,p) = 0) ∧
      ∀ y, (∀ x, f (y,x) = 0) → ∀ x, U (y,x) = 0 ∧ V (y,x) = 0 := by
  obtain ⟨U,V,hU,hV,hUc,hVc,hcurl,huvzero⟩ := exists_parametric_compact_primitive hf hfc hf0
  let alpha : P × Plane → Plane →L[ℝ] ℝ := fun p =>
    coordinateForm (fun x => U (p.1,x)) (fun x => V (p.1,x)) p.2
  have has : ContDiff ℝ ∞ alpha :=
    (hU.smul contDiff_const).add (hV.smul contDiff_const)
  have hac : HasCompactSupport alpha := by
    apply HasCompactSupport.intro (hUc.union hVc)
    intro p hp
    have hu : U p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (Or.inl h))
    have hv : V p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (Or.inr h))
    change U p • _ + V p • _ = 0
    rw [hu,hv,zero_smul,zero_smul,zero_add]
  have hc (y : P) (p : Plane) : planarCurl (fun x => alpha (y,x)) p = f (y,p) :=
    (coordinateForm_curl (hU.comp (contDiff_const.prodMk contDiff_id))
      (hV.comp (contDiff_const.prodMk contDiff_id)) p).trans (hcurl y p)
  have hz' (i : ι) (y : P) : (∫ p in roundDisk (R i), planarCurl (fun x => alpha (y,x)) p) = 0 := by
    simp_rw [hc]
    exact hz i y
  obtain ⟨beta,hbs,hbc,hcurlb,hbt,hbzero⟩ :=
    exists_parametric_finite_circle_correction has hac R hR hRi hz'
  let U' : P × Plane → ℝ := fun p => beta p (1,0)
  let V' : P × Plane → ℝ := fun p => beta p (0,1)
  have hUs : ContDiff ℝ ∞ U' := hbs.clm_apply contDiff_const
  have hVs : ContDiff ℝ ∞ V' := hbs.clm_apply contDiff_const
  have hU'c : HasCompactSupport U' := by
    apply HasCompactSupport.intro hbc
    intro p hp
    simp only [U',image_eq_zero_of_notMem_tsupport hp,zero_apply]
  have hV'c : HasCompactSupport V' := by
    apply HasCompactSupport.intro hbc
    intro p hp
    simp only [V',image_eq_zero_of_notMem_tsupport hp,zero_apply]
  have hUy (y : P) : ContDiff ℝ ∞ (fun x => U' (y,x)) := hUs.comp (contDiff_const.prodMk contDiff_id)
  have hVy (y : P) : ContDiff ℝ ∞ (fun x => V' (y,x)) := hVs.comp (contDiff_const.prodMk contDiff_id)
  have hby (y : P) : ContDiff ℝ ∞ (fun x => beta (y,x)) := hbs.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨U',V',hUs,hVs,hU'c,hV'c,?_,?_,?_⟩
  · intro y p
    rw [plane_deriv_first ((hVy y).differentiable (by simp)),
      plane_deriv_second ((hUy y).differentiable (by simp))]
    change fderiv ℝ (fun q => beta (y,q) (0,1)) p (1,0) -
      fderiv ℝ (fun q => beta (y,q) (1,0)) p (0,1) = f (y,p)
    rw [form_eval_fderiv (hby y),form_eval_fderiv (hby y)]
    exact (hcurlb y p).trans (hc y p)
  · intro i y p hp
    have he : (-p.2,p.1) = (-p.2) • ((1:ℝ),(0:ℝ)) + p.1 • ((0:ℝ),(1:ℝ)) := by
      ext <;> simp
    have ht := hbt i y p hp
    rw [he,map_add,map_smul,map_smul] at ht
    exact ht

  · intro y hy x
    have ha0 (q : Plane) : alpha (y,q) = 0 := by
      obtain ⟨hu,hv⟩ := huvzero y hy q
      simp only [alpha,coordinateForm,hu,hv,zero_smul,zero_add]
    have hb0 := hbzero y ha0 x
    simp only [U',V',hb0,zero_apply,and_self]

omit [FiniteDimensional ℝ P] in

theorem parametric_backgroundField_smooth {g f U V : P × Plane → ℝ}
    (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (hgpos : ∀ p, 0 < g p) (hpos : ∀ p, 0 < g p+f p) :
    ContDiff ℝ ∞ (fun p : ℝ × (P × Plane) =>
      backgroundField (fun x => g (p.2.1,x)) (fun x => f (p.2.1,x))
        (fun x => U (p.2.1,x)) (fun x => V (p.2.1,x)) (p.1,p.2.2)) := by
  have hb : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hβ : ContDiff ℝ ∞ (deriv Real.smoothTransition) := (contDiff_infty_iff_deriv.mp hb).2
  have hd : ContDiff ℝ ∞ (fun p : ℝ × (P × Plane) =>
      g p.2 + Real.smoothTransition p.1 * f p.2) :=
    (hg.comp contDiff_snd).add ((hb.comp contDiff_fst).mul (hf.comp contDiff_snd))
  have hdpos (p : ℝ × (P × Plane)) : 0 < g p.2 + Real.smoothTransition p.1 * f p.2 :=
    backgroundDensity_positive (fun x => hgpos (p.2.1,x)) (fun x => hpos (p.2.1,x)) (p.1,p.2.2)
  exact (((hβ.comp contDiff_fst).neg.mul (hV.comp contDiff_snd)).div hd (fun p => (hdpos p).ne')).prodMk
    (((hβ.comp contDiff_fst).mul (hU.comp contDiff_snd)).div hd (fun p => (hdpos p).ne'))

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem parametric_backgroundField_compact {g f U V : P × Plane → ℝ}
    (hU : HasCompactSupport U) (hV : HasCompactSupport V) :
    HasCompactSupport (fun p : ℝ × (P × Plane) =>
      backgroundField (fun x => g (p.2.1,x)) (fun x => f (p.2.1,x))
        (fun x => U (p.2.1,x)) (fun x => V (p.2.1,x)) (p.1,p.2.2)) := by
  apply HasCompactSupport.intro (smoothTransition_deriv_compact.prod (hU.union hV))
  intro p hp
  have hn : p.1 ∉ tsupport (deriv Real.smoothTransition) ∨ p.2 ∉ tsupport U ∪ tsupport V := by
    simpa only [mem_prod,not_and_or] using hp
  rcases hn with ht | hx
  · simp [backgroundField,image_eq_zero_of_notMem_tsupport ht]
  · have hu : U p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h))
    have hv : V p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))
    simp [backgroundField,hu,hv]

theorem exists_parametric_relative_background_moser {ι : Type*} [Fintype ι]
    {g f : P × Plane → ℝ} (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hf0 : ∀ y, (∫ p, f (y,p)) = 0)
    (hgpos : ∀ p, 0 < g p) (hpos : ∀ p, 0 < g p+f p)
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) (hRi : Injective R)
    (hz : ∀ i y, (∫ p in roundDisk (R i), f (y,p)) = 0) :
    ∃ Φ : P → Plane ≃ₜ Plane,
      ContDiff ℝ ∞ (fun p : P × Plane => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : P × Plane => (Φ p.1).symm p.2) ∧
      HasCompactSupport (fun p : P × Plane => Φ p.1 p.2-p.2) ∧
      (∀ y x v w, (g (y,Φ y x)+f (y,Φ y x)) *
        planarArea (fderiv ℝ (Φ y) x v) (fderiv ℝ (Φ y) x w) = g (y,x)*planarArea v w) ∧
      (∀ i y, Φ y '' closedRoundDisk (R i) = closedRoundDisk (R i)) ∧
      ∀ y, (∀ x, f (y,x) = 0) → ∀ x, Φ y x = x := by
  obtain ⟨U,V,hU,hV,hUc,hVc,hcurl,htan,huvzero⟩ :=
    exists_parametric_relative_primitive hf hfc hf0 R hR hRi hz
  let field : ℝ × (P × Plane) → Plane := fun p =>
    backgroundField (fun x => g (p.2.1,x)) (fun x => f (p.2.1,x))
      (fun x => U (p.2.1,x)) (fun x => V (p.2.1,x)) (p.1,p.2.2)
  have hXs : ContDiff ℝ ∞ field := parametric_backgroundField_smooth hg hf hU hV hgpos hpos
  have hXc : HasCompactSupport field := parametric_backgroundField_compact hUc hVc
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by simp)
  let X : C(ℝ × (P × Plane),Plane) := ⟨field,hXs.continuous⟩
  have hgy (y : P) : ContDiff ℝ ∞ (fun x => g (y,x)) := hg.comp (contDiff_const.prodMk contDiff_id)
  have hfy (y : P) : ContDiff ℝ ∞ (fun x => f (y,x)) := hf.comp (contDiff_const.prodMk contDiff_id)
  have hUy (y : P) : ContDiff ℝ ∞ (fun x => U (y,x)) := hU.comp (contDiff_const.prodMk contDiff_id)
  have hVy (y : P) : ContDiff ℝ ∞ (fun x => V (y,x)) := hV.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨Φ,hΦ,hΦi,hΦc,hΦarea,hΦdisk,hΦfix⟩ := exists_parametric_density_transport X hL hXs hXc
    (fun y => backgroundDensity (fun x => g (y,x)) (fun x => f (y,x)))
    (fun y => backgroundDensity_smooth (hgy y) (hfy y)) planarArea
    (fun y => backgroundField_transport (hgy y) (hfy y) (hUy y) (hVy y)
      (fun x => hgpos (y,x)) (fun x => hpos (y,x)) (hcurl y)) R hR
    (fun i y => backgroundField_tangent (g := fun x => g (y,x))
      (f := fun x => f (y,x)) (htan i y)) 0 1
  refine ⟨Φ,hΦ,hΦi,hΦc,?_,hΦdisk,?_⟩
  · intro y x v w
    simpa only [zero_add,backgroundDensity,Real.smoothTransition.one,Real.smoothTransition.zero,
      one_mul,zero_mul,add_zero] using hΦarea y x v w
  · intro y hy x
    apply hΦfix y _ x
    intro t q
    obtain ⟨hu,hv⟩ := huvzero y hy q
    change backgroundField (fun x => g (y,x)) (fun x => f (y,x))
      (fun x => U (y,x)) (fun x => V (y,x)) (t,q) = 0
    simp only [backgroundField,hu,hv,mul_zero,zero_div]
    rfl

end

def radialDiskChart (R : ℝ) : OpenPartialHomeomorph Plane Plane :=
  (Complex.equivRealProdCLM.symm.toHomeomorph.toOpenPartialHomeomorph.trans
    (OpenPartialHomeomorph.univBall (0:ℂ) R)).trans
    Complex.equivRealProdCLM.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem radialDiskChart_source (R : ℝ) : (radialDiskChart R).source = univ := by
  simp only [radialDiskChart,OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source,OpenPartialHomeomorph.univBall_source,
    preimage_univ,inter_self]

theorem radialDiskChart_target {R : ℝ} (hR : 0 < R) :
    (radialDiskChart R).target = roundDisk R := by
  simp only [radialDiskChart,OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target,OpenPartialHomeomorph.univBall_target _ hR,
    preimage_univ,inter_univ,univ_inter]
  ext p
  simp only [mem_preimage,Metric.mem_ball,dist_zero_right]
  change ‖Complex.equivRealProdCLM.symm p‖ < R ↔ radiusSq p < R^2
  rw [← complex_normSq_plane]
  exact (sq_lt_sq₀ (norm_nonneg _) hR.le).symm

theorem radialDiskChart_apply {R : ℝ} (hR : 0 < R) (p : Plane) :
    radialDiskChart R p = (R / Real.sqrt (1+radiusSq p)) • p := by
  change Complex.equivRealProdCLM
    (OpenPartialHomeomorph.univBall (0:ℂ) R (Complex.equivRealProdCLM.symm p)) = _
  simp only [OpenPartialHomeomorph.univBall,dite_eq_left hR]
  change Complex.equivRealProdCLM
    (R • ((Real.sqrt (1+‖Complex.equivRealProdCLM.symm p‖^2))⁻¹ •
      Complex.equivRealProdCLM.symm p) + 0) = _
  rw [add_zero,map_smul,map_smul,ContinuousLinearEquiv.apply_symm_apply,
    complex_normSq_plane,smul_smul,div_eq_mul_inv]

theorem radialDiskChart_smooth (R : ℝ) : ContDiff ℝ ∞ (radialDiskChart R) :=
  Complex.equivRealProdCLM.contDiff.comp
    (OpenPartialHomeomorph.contDiff_univBall.comp Complex.equivRealProdCLM.symm.contDiff)

theorem radialDiskChart_symm_smooth {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ ∞ (radialDiskChart R).symm (roundDisk R) := by
  apply Complex.equivRealProdCLM.contDiff.comp_contDiffOn
  apply OpenPartialHomeomorph.contDiffOn_univBall_symm.comp
    Complex.equivRealProdCLM.symm.contDiff.contDiffOn
  intro p hp
  rw [Metric.mem_ball,dist_zero_right]
  have hs : ‖Complex.equivRealProdCLM.symm p‖^2 < R^2 := by
    rw [complex_normSq_plane]
    exact hp
  exact (sq_lt_sq₀ (norm_nonneg _) hR.le).mp hs

@[simp] theorem radiusSq_nonneg (p : Plane) : 0 ≤ radiusSq p :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem radialDiskChart_fderiv {R : ℝ} (hR : 0 < R) (p v : Plane) :
    fderiv ℝ (radialDiskChart R) p v =
      (R / Real.sqrt (1+radiusSq p)) • v -
        (R / (Real.sqrt (1+radiusSq p))^3 * (p.1*v.1+p.2*v.2)) • p := by
  have hp : 0 < 1+radiusSq p := by have := radiusSq_nonneg p; linarith
  have hs : Real.sqrt (1+radiusSq p) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hq := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).pow 2
  have hr := (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2
  have hd := HasFDerivAt.const_add 1 (hq.add hr)
  have hds := hd.sqrt hp.ne'
  have hdi := (hasDerivAt_inv hs).comp_hasFDerivAt p hds
  have hdc := hdi.const_mul R
  have he := hdc.smul (hasFDerivAt_id p)
  have hfun : (fun q : Plane => (R * (Real.sqrt (1+(q.1^2+q.2^2)))⁻¹) • q) =
      radialDiskChart R := by
    funext q
    rw [radialDiskChart_apply hR]
    rfl
  change HasFDerivAt (fun q : Plane => (R * (Real.sqrt (1+(q.1^2+q.2^2)))⁻¹) • q) _ p at he
  rw [hfun] at he
  rw [he.fderiv]
  ext <;> simp [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    Prod.smul_def,smul_eq_mul,radiusSq] <;> field_simp <;> ring

def radialDiskDensity (R : ℝ) (p : Plane) : ℝ := R^2/(1+radiusSq p)^2

theorem radialDiskDensity_pos {R : ℝ} (hR : 0 < R) (p : Plane) :
    0 < radialDiskDensity R p := by
  exact div_pos (sq_pos_of_pos hR) (sq_pos_of_pos (by have := radiusSq_nonneg p; linarith))

theorem radialDiskDensity_smooth (R : ℝ) : ContDiff ℝ ∞ (radialDiskDensity R) := by
  apply contDiff_const.div ((contDiff_const.add radiusSq_smooth).pow 2)
  intro p
  exact pow_ne_zero _ (by have := radiusSq_nonneg p; positivity)

theorem planarArea_radial_rank_one (a b : ℝ) (p v w : Plane) :
    planarArea (a • v - (b * (p.1*v.1+p.2*v.2)) • p)
      (a • w - (b * (p.1*w.1+p.2*w.2)) • p) =
      (a^2-a*b*radiusSq p)*planarArea v w := by
  change (a*v.1-b*(p.1*v.1+p.2*v.2)*p.1)*(a*w.2-b*(p.1*w.1+p.2*w.2)*p.2) -
    (a*v.2-b*(p.1*v.1+p.2*v.2)*p.2)*(a*w.1-b*(p.1*w.1+p.2*w.2)*p.1) =
      (a^2-a*b*(p.1^2+p.2^2))*(v.1*w.2-v.2*w.1)
  ring

theorem radialDiskChart_area {R : ℝ} (hR : 0 < R) (p v w : Plane) :
    planarArea (fderiv ℝ (radialDiskChart R) p v)
      (fderiv ℝ (radialDiskChart R) p w) = radialDiskDensity R p * planarArea v w := by
  rw [radialDiskChart_fderiv hR,radialDiskChart_fderiv hR,planarArea_radial_rank_one]
  congr 1
  have hp : 0 < 1+radiusSq p := by have := radiusSq_nonneg p; linarith
  have hs : Real.sqrt (1+radiusSq p) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hs2 := Real.sq_sqrt hp.le
  unfold radialDiskDensity
  generalize Real.sqrt (1+radiusSq p) = s at *
  rw [show radiusSq p = s^2-1 by linarith]
  field_simp
  ring

theorem radiusSq_smul (a : ℝ) (p : Plane) : radiusSq (a • p) = a^2*radiusSq p := by
  change (a*p.1)^2+(a*p.2)^2 = a^2*(p.1^2+p.2^2)
  ring

theorem radialDiskChart_radiusSq {R : ℝ} (hR : 0 < R) (p : Plane) :
    radiusSq (radialDiskChart R p) = R^2*radiusSq p/(1+radiusSq p) := by
  rw [radialDiskChart_apply hR,radiusSq_smul,div_pow,Real.sq_sqrt]
  · ring
  · have := radiusSq_nonneg p
    linarith

def diskChartRadius (R r : ℝ) : ℝ := r / Real.sqrt (R^2-r^2)

theorem diskChartRadius_pos {R r : ℝ} (hr : 0 < r) (hrR : r < R) :
    0 < diskChartRadius R r := by
  apply div_pos hr
  apply Real.sqrt_pos.mpr
  nlinarith

theorem radialDiskChart_closed_iff {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (p : Plane) : radialDiskChart R p ∈ closedRoundDisk r ↔
      p ∈ closedRoundDisk (diskChartRadius R r) := by
  change radiusSq (radialDiskChart R p) ≤ r^2 ↔ radiusSq p ≤ _
  have hd : 0 < R^2-r^2 := by nlinarith
  have hp : 0 < 1+radiusSq p := by have := radiusSq_nonneg p; linarith
  rw [radialDiskChart_radiusSq hR,div_le_iff₀ hp]
  change _ ↔ radiusSq p ≤ (r/Real.sqrt (R^2-r^2))^2
  rw [div_pow,Real.sq_sqrt hd.le,le_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith

theorem radialDiskChart_open_iff {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (p : Plane) : radialDiskChart R p ∈ roundDisk r ↔
      p ∈ roundDisk (diskChartRadius R r) := by
  change radiusSq (radialDiskChart R p) < r^2 ↔ radiusSq p < _
  have hd : 0 < R^2-r^2 := by nlinarith
  have hp : 0 < 1+radiusSq p := by have := radiusSq_nonneg p; linarith
  rw [radialDiskChart_radiusSq hR,div_lt_iff₀ hp]
  change _ ↔ radiusSq p < (r/Real.sqrt (R^2-r^2))^2
  rw [div_pow,Real.sq_sqrt hd.le,lt_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith

theorem radialDiskChart_image_closed {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R) :
    radialDiskChart R '' closedRoundDisk (diskChartRadius R r) = closedRoundDisk r := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (radialDiskChart_closed_iff hR hr hrR q).mpr hq
  · intro hp
    have ht : p ∈ (radialDiskChart R).target := by
      rw [radialDiskChart_target hR]
      change radiusSq p < R^2
      change radiusSq p ≤ r^2 at hp
      nlinarith
    refine ⟨(radialDiskChart R).symm p,?_,(radialDiskChart R).right_inv ht⟩
    apply (radialDiskChart_closed_iff hR hr hrR _).mp
    rw [(radialDiskChart R).right_inv ht]
    exact hp

theorem radialDiskChart_image_open {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R) :
    radialDiskChart R '' roundDisk (diskChartRadius R r) = roundDisk r := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (radialDiskChart_open_iff hR hr hrR q).mpr hq
  · intro hp
    have ht : p ∈ (radialDiskChart R).target := by
      rw [radialDiskChart_target hR]
      change radiusSq p < R^2
      change radiusSq p < r^2 at hp
      nlinarith
    refine ⟨(radialDiskChart R).symm p,?_,(radialDiskChart R).right_inv ht⟩
    apply (radialDiskChart_open_iff hR hr hrR _).mp
    rw [(radialDiskChart R).right_inv ht]
    exact hp

theorem diskChartRadius_strictMonoOn {R : ℝ} (hR : 0 < R) :
    StrictMonoOn (diskChartRadius R) (Ico 0 R) := by
  intro r hr s hs hrs
  have hdr : 0 < R^2-r^2 := by nlinarith [hr.1,hr.2]
  have hds : 0 < R^2-s^2 := by nlinarith [hs.1,hs.2]
  have hnr : 0 ≤ diskChartRadius R r := div_nonneg hr.1 (Real.sqrt_nonneg _)
  have hns : 0 ≤ diskChartRadius R s := div_nonneg hs.1 (Real.sqrt_nonneg _)
  apply (sq_lt_sq₀ hnr hns).mp
  change (r/Real.sqrt (R^2-r^2))^2 < (s/Real.sqrt (R^2-s^2))^2
  rw [div_pow,div_pow,Real.sq_sqrt hdr.le,Real.sq_sqrt hds.le,div_lt_div_iff₀ hdr hds]
  nlinarith [mul_pos (sq_pos_of_pos hR) (show 0 < s^2-r^2 by nlinarith [hr.1])]

theorem planar_det (A : Plane →L[ℝ] Plane) :
    A.det = planarArea (A (1,0)) (A (0,1)) := by
  let b : Module.Basis (Fin 2) ℝ Plane :=
    Module.Basis.ofEquivFun (LinearEquiv.finTwoArrow ℝ ℝ).symm
  change LinearMap.det A.toLinearMap = _
  rw [← LinearMap.det_toMatrix b,Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,b,Module.Basis.coe_ofEquivFun,
    LinearEquiv.finTwoArrow,planarArea_apply]
  ring

theorem radialDiskChart_det {R : ℝ} (hR : 0 < R) (p : Plane) :
    (fderiv ℝ (radialDiskChart R) p).det = radialDiskDensity R p := by
  rw [planar_det,radialDiskChart_area hR]
  simp [planarArea_apply]

theorem radialDiskChart_integral {R : ℝ} (hR : 0 < R) (f : Plane → ℝ) :
    (∫ x in roundDisk R, f x) = ∫ x, radialDiskDensity R x*f (radialDiskChart R x) := by
  have he := integral_target_eq_integral_abs_det_fderiv_smul volume
    (f := radialDiskChart R) (f' := fderiv ℝ (radialDiskChart R))
    (fun x _ => (((radialDiskChart_smooth R).differentiable (by simp)) x).hasFDerivAt) f
  simpa only [radialDiskChart_target hR,radialDiskChart_source,setIntegral_univ,
    radialDiskChart_det hR,abs_of_pos (radialDiskDensity_pos hR _),smul_eq_mul] using he

theorem radialDiskChart_integral_inner {R r : ℝ} (hR : 0 < R)
    (hr : 0 ≤ r) (hrR : r < R) (f : Plane → ℝ) :
    (∫ x in roundDisk r, f x) = ∫ x in roundDisk (diskChartRadius R r),
      radialDiskDensity R x*f (radialDiskChart R x) := by
  have hm : MeasurableSet (roundDisk (diskChartRadius R r)) :=
    (isOpen_lt radiusSq_smooth.continuous continuous_const).measurableSet
  have hinj : InjOn (radialDiskChart R) (roundDisk (diskChartRadius R r)) :=
    (radialDiskChart R).injOn.mono (by rw [radialDiskChart_source]; exact subset_univ _)
  have he := integral_image_eq_integral_abs_det_fderiv_smul volume hm
    (f' := fderiv ℝ (radialDiskChart R))
    (fun x _ => (((radialDiskChart_smooth R).differentiable (by simp)) x).hasFDerivAt.hasFDerivWithinAt)
    hinj f
  simpa only [radialDiskChart_image_open hR hr hrR,radialDiskChart_det hR,
    abs_of_pos (radialDiskDensity_pos hR _),smul_eq_mul] using he

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Chart
open scoped ContDiff Topology
open Set Function

variable {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def conjugate (c : OpenPartialHomeomorph E F) (φ : E → E) (x : F) : F := by
  classical
  exact if x ∈ c.target then c (φ (c.symm x)) else x

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem conjugate_of_mem (c : OpenPartialHomeomorph E F) (φ : E → E)
    {x : F} (hx : x ∈ c.target) : conjugate c φ x = c (φ (c.symm x)) := by
  simp [conjugate,hx]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem conjugate_of_notMem (c : OpenPartialHomeomorph E F) (φ : E → E)
    {x : F} (hx : x ∉ c.target) : conjugate c φ x = x := by
  simp [conjugate,hx]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem conjugate_apply (c : OpenPartialHomeomorph E F) (hc : c.source = univ)
    (φ : E → E) (x : E) : conjugate c φ (c x) = c (φ x) := by
  have hx : x ∈ c.source := by rw [hc]; trivial
  rw [conjugate_of_mem c φ (c.map_source hx),c.left_inv hx]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem conjugate_comp (c : OpenPartialHomeomorph E F) (hc : c.source = univ)
    (φ ψ : E → E) (x : F) :
    conjugate c φ (conjugate c ψ x) = conjugate c (φ ∘ ψ) x := by
  by_cases hx : x ∈ c.target
  · rw [conjugate_of_mem c ψ hx,conjugate_apply c hc,
      conjugate_of_mem c (φ ∘ ψ) hx]
    rfl
  · simp only [conjugate_of_notMem c _ hx]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem conjugate_id (c : OpenPartialHomeomorph E F) (x : F) :
    conjugate c id x = x := by
  by_cases hx : x ∈ c.target
  · rw [conjugate_of_mem c id hx]
    exact c.right_inv hx
  · exact conjugate_of_notMem c id hx

def conjugateEquiv (c : OpenPartialHomeomorph E F) (hc : c.source = univ)
    (φ : E ≃ E) : F ≃ F where
  toFun := conjugate c φ
  invFun := conjugate c φ.symm
  left_inv x := by
    rw [conjugate_comp c hc]
    have he : ((φ.symm : E → E) ∘ (φ : E → E)) = id := funext φ.symm_apply_apply
    rw [he,conjugate_id]
  right_inv x := by
    rw [conjugate_comp c hc]
    have he : ((φ : E → E) ∘ (φ.symm : E → E)) = id := funext φ.apply_symm_apply
    rw [he,conjugate_id]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup P] [NormedSpace ℝ P] in

theorem conjugate_eq_of_notMem_image (c : OpenPartialHomeomorph E F)
    (φ : P → E → E) {K : Set (P × E)}
    (hK : ∀ p : P × E, p ∉ K → φ p.1 p.2 = p.2)
    {p : P × F} (hp : p ∉ (fun q : P × E => (q.1,c q.2)) '' K) :
    conjugate c (φ p.1) p.2 = p.2 := by
  by_cases hx : p.2 ∈ c.target
  · rw [conjugate_of_mem c _ hx]
    have hq : (p.1,c.symm p.2) ∉ K := by
      intro h
      apply hp
      exact ⟨(p.1,c.symm p.2),h,by simp only [c.right_inv hx]⟩
    rw [hK _ hq,c.right_inv hx]
  · exact conjugate_of_notMem c _ hx

theorem conjugate_smooth_compact (c : OpenPartialHomeomorph E F)
    (hcs : c.source = univ) (hc : ContDiff ℝ ∞ c)
    (hci : ContDiffOn ℝ ∞ c.symm c.target)
    (φ : P → E → E) (hφ : ContDiff ℝ ∞ (fun p : P × E => φ p.1 p.2))
    (hφc : HasCompactSupport (fun p : P × E => φ p.1 p.2-p.2)) :
    ContDiff ℝ ∞ (fun p : P × F => conjugate c (φ p.1) p.2) ∧
      HasCompactSupport (fun p : P × F => conjugate c (φ p.1) p.2-p.2) ∧
      tsupport (fun p : P × F => conjugate c (φ p.1) p.2-p.2) ⊆
        (fun q : P × E => (q.1,c q.2)) '' tsupport (fun p : P × E => φ p.1 p.2-p.2) := by
  let K : Set (P × F) := (fun q : P × E => (q.1,c q.2)) ''
    tsupport (fun p : P × E => φ p.1 p.2-p.2)
  have hK : IsCompact K := hφc.image (continuous_fst.prodMk (hc.continuous.comp continuous_snd))
  have he (p : P × F) (hp : p ∉ K) : conjugate c (φ p.1) p.2 = p.2 := by
    apply conjugate_eq_of_notMem_image c φ (K := tsupport (fun p : P × E => φ p.1 p.2-p.2)) _ hp
    intro q hq
    exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun p : P × E => φ p.1 p.2-p.2) hq)
  have hsupport : tsupport (fun p : P × F => conjugate c (φ p.1) p.2-p.2) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro p hp
    by_contra h
    exact hp (sub_eq_zero.mpr (he p h))
  refine ⟨?_,hK.of_isClosed_subset (isClosed_tsupport _) hsupport,hsupport⟩
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2 ∈ c.target
  · have hi := (hci p.2 hp).contDiffAt (c.open_target.mem_nhds hp)
    have hd := hc.contDiffAt.comp p (hφ.contDiffAt.comp p
      (contDiffAt_fst.prodMk (hi.comp p contDiffAt_snd)))
    apply hd.congr_of_eventuallyEq
    filter_upwards [(c.open_target.preimage continuous_snd).mem_nhds hp] with q hq
    exact conjugate_of_mem c _ hq
  · have hn : p ∉ K := by
      rintro ⟨q,hq,rfl⟩
      exact hp (c.map_source (by rw [hcs]; trivial))
    apply contDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hn] with q hq
    exact he q hq

omit [NormedSpace ℝ E] [NormedSpace ℝ P] in
theorem inverse_displacement_compact (φ : P → E ≃ₜ E)
    (hφ : HasCompactSupport (fun p : P × E => φ p.1 p.2-p.2)) :
    HasCompactSupport (fun p : P × E => (φ p.1).symm p.2-p.2) := by
  apply HasCompactSupport.intro hφ
  intro p hp
  have he : φ p.1 p.2 = p.2 := sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun p : P × E => φ p.1 p.2-p.2) hp)
  rw [sub_eq_zero]
  apply (φ p.1).injective
  rw [(φ p.1).apply_symm_apply,he]

def conjugateHomeomorph (c : OpenPartialHomeomorph E F)
    (hcs : c.source = univ) (hc : ContDiff ℝ ∞ c)
    (hci : ContDiffOn ℝ ∞ c.symm c.target)
    (φ : E ≃ₜ E) (hφ : ContDiff ℝ ∞ φ) (hφi : ContDiff ℝ ∞ φ.symm)
    (hφc : HasCompactSupport (fun p : E => φ p-p)) : F ≃ₜ F where
  toEquiv := conjugateEquiv c hcs φ.toEquiv
  continuous_toFun := by
    have hj : ContDiff ℝ ∞ (fun p : (Fin 0 → ℝ) × E => φ p.2) := hφ.comp contDiff_snd
    have hk : HasCompactSupport (fun p : (Fin 0 → ℝ) × E => φ p.2-p.2) := by
      apply HasCompactSupport.intro ((isCompact_univ : IsCompact (univ : Set (Fin 0 → ℝ))).prod hφc)
      intro p hp
      exact image_eq_zero_of_notMem_tsupport (f := fun q : E => φ q-q)
        (fun h => hp ⟨mem_univ _,h⟩)
    have hs := (conjugate_smooth_compact c hcs hc hci (fun _ : Fin 0 → ℝ => φ) hj hk).1
    exact (hs.comp ((contDiff_const (c := (0 : Fin 0 → ℝ))).prodMk contDiff_id)).continuous
  continuous_invFun := by
    have hj : ContDiff ℝ ∞ (fun p : (Fin 0 → ℝ) × E => φ.symm p.2) := hφi.comp contDiff_snd
    have hk : HasCompactSupport (fun p : (Fin 0 → ℝ) × E => φ p.2-p.2) := by
      apply HasCompactSupport.intro ((isCompact_univ : IsCompact (univ : Set (Fin 0 → ℝ))).prod hφc)
      intro p hp
      exact image_eq_zero_of_notMem_tsupport (f := fun q : E => φ q-q)
        (fun h => hp ⟨mem_univ _,h⟩)
    have hki := inverse_displacement_compact (fun _ : Fin 0 → ℝ => φ) hk
    have hs := (conjugate_smooth_compact c hcs hc hci (fun _ : Fin 0 → ℝ => φ.symm) hj hki).1
    exact (hs.comp ((contDiff_const (c := (0 : Fin 0 → ℝ))).prodMk contDiff_id)).continuous

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem conjugate_image (c : OpenPartialHomeomorph E F) (hc : c.source = univ)
    (φ : E → E) (A : Set E) : conjugate c φ '' (c '' A) = c '' (φ '' A) := by
  rw [image_image,image_image]
  apply image_congr
  intro x _
  exact conjugate_apply c hc φ x

theorem conjugate_contDiffAt_of_mem (c : OpenPartialHomeomorph E F)
    (hc : ContDiff ℝ ∞ c) (hci : ContDiffOn ℝ ∞ c.symm c.target)
    (φ : E → E) (hφ : ContDiff ℝ ∞ φ) {x : F} (hx : x ∈ c.target) :
    ContDiffAt ℝ ∞ (conjugate c φ) x := by
  have hi := (hci x hx).contDiffAt (c.open_target.mem_nhds hx)
  have hd := hc.contDiffAt.comp x (hφ.contDiffAt.comp x hi)
  apply hd.congr_of_eventuallyEq
  filter_upwards [c.open_target.mem_nhds hx] with q hq
  exact conjugate_of_mem c φ hq

theorem chart_fderiv_right_inverse (c : OpenPartialHomeomorph E F)
    (hc : ContDiff ℝ ∞ c) (hci : ContDiffOn ℝ ∞ c.symm c.target)
    {x : F} (hx : x ∈ c.target) (v : F) :
    fderiv ℝ c (c.symm x) (fderiv ℝ c.symm x v) = v := by
  have hi := ((hci x hx).contDiffAt (c.open_target.mem_nhds hx)).differentiableAt (by simp)
  have hd := ((hc.differentiable (by simp)) _).hasFDerivAt.comp x hi.hasFDerivAt
  have he : (id : F → F) =ᶠ[𝓝 x] (c ∘ c.symm) := by
    filter_upwards [c.open_target.mem_nhds hx] with q hq
    exact (c.right_inv hq).symm
  have hder := (hd.congr_of_eventuallyEq he).fderiv
  have hv := congrArg (fun L : F →L[ℝ] F => L v) hder
  simpa only [fderiv_id,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply] using hv.symm

theorem conjugate_fderiv_chart (c : OpenPartialHomeomorph E F)
    (hcs : c.source = univ) (hc : ContDiff ℝ ∞ c)
    (hci : ContDiffOn ℝ ∞ c.symm c.target)
    (φ : E → E) (hφ : ContDiff ℝ ∞ φ) (x v : E) :
    fderiv ℝ (conjugate c φ) (c x) (fderiv ℝ c x v) =
      fderiv ℝ c (φ x) (fderiv ℝ φ x v) := by
  have hx : c x ∈ c.target := c.map_source (by rw [hcs]; trivial)
  have hd := (conjugate_contDiffAt_of_mem c hc hci φ hφ hx).differentiableAt (by simp)
  have hl := hd.hasFDerivAt.comp x (((hc.differentiable (by simp)) x).hasFDerivAt)
  have hr := (((hc.differentiable (by simp)) (φ x)).hasFDerivAt).comp x
    (((hφ.differentiable (by simp)) x).hasFDerivAt)
  have he : (conjugate c φ ∘ c) = (c ∘ φ) := funext (conjugate_apply c hcs φ)
  rw [he] at hl
  have hder := hl.unique hr
  exact congrArg (fun L : E →L[ℝ] F => L v) hder

omit [NormedSpace ℝ E] [NormedSpace ℝ P] in
theorem fiber_displacement_compact (φ : P → E → E)
    (hφ : HasCompactSupport (fun p : P × E => φ p.1 p.2-p.2)) (y : P) :
    HasCompactSupport (fun p : E => φ y p-p) := by
  apply HasCompactSupport.intro (hφ.image continuous_snd)
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (f := fun p : P × E => φ p.1 p.2-p.2)
    (fun h => hx ⟨(y,x),h,rfl⟩)

theorem exists_conjugate_family (c : OpenPartialHomeomorph E F)
    (hcs : c.source = univ) (hc : ContDiff ℝ ∞ c)
    (hci : ContDiffOn ℝ ∞ c.symm c.target)
    (Φ : P → E ≃ₜ E) (hΦ : ContDiff ℝ ∞ (fun p : P × E => Φ p.1 p.2))
    (hΦi : ContDiff ℝ ∞ (fun p : P × E => (Φ p.1).symm p.2))
    (hΦc : HasCompactSupport (fun p : P × E => Φ p.1 p.2-p.2)) :
    ∃ Ψ : P → F ≃ₜ F,
      (∀ y x, Ψ y x = conjugate c (Φ y) x) ∧
      ContDiff ℝ ∞ (fun p : P × F => Ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : P × F => (Ψ p.1).symm p.2) ∧
      HasCompactSupport (fun p : P × F => Ψ p.1 p.2-p.2) ∧
      tsupport (fun p : P × F => Ψ p.1 p.2-p.2) ⊆
        univ ×ˢ c.target := by
  let Ψ : P → F ≃ₜ F := fun y => conjugateHomeomorph c hcs hc hci (Φ y)
    (hΦ.comp (contDiff_const.prodMk contDiff_id))
    (hΦi.comp (contDiff_const.prodMk contDiff_id))
    (fiber_displacement_compact (fun y => Φ y) hΦc y)
  have hs := conjugate_smooth_compact c hcs hc hci (fun y => Φ y) hΦ hΦc
  have hsi := conjugate_smooth_compact c hcs hc hci (fun y => (Φ y).symm) hΦi
    (inverse_displacement_compact Φ hΦc)
  refine ⟨Ψ,fun _ _ => rfl,hs.1,hsi.1,hs.2.1,?_⟩
  intro p hp
  obtain ⟨q,_,rfl⟩ := hs.2.2 hp
  exact ⟨mem_univ _,c.map_source (by rw [hcs]; trivial)⟩

end PackingSufficiencySupport.Chart
end

end OAI
