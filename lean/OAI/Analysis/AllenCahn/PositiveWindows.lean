import OAI.Analysis.AllenCahn.ExtremeWindows

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open DeGiorgiCompactness (JetSpace CoherentJets pdeJetCone jetDirectional jetSegmentMass)

lemma conePotential_positive_window {n : ℕ} {ν : Space n} (hν : ‖ν‖=1)
    {c : ℝ} (hc : 3/4 < c) :
    ∃ R > (0 : ℝ), ∀ f ∈ positiveLinearCone (conePotential ν),
      |fderiv ℝ f 0 (Real.sqrt 2 • ν)| ≤
        c*(∫ y in -R..R, f (y • (Real.sqrt 2 • ν))*sech y^4) := by
  obtain ⟨R,hR,hbound⟩ := conePotential_extreme_window hc
  have hK := conePotential_jetCone_compact hν
  have hw : Continuous (fun y : ℝ => sech y^4) := contDiff_sech.continuous.pow 4
  have H (s : ℝ) (hs : s=1 ∨ s= -1) :=
    DeGiorgiCompactness.jetCone_window_of_extreme hK (Real.sqrt 2 • ν) hw hR.le c s
      (fun g hg => by
        have he := hbound hν g hg
        rcases hs with rfl | rfl
        · simpa only [one_mul] using (le_abs_self _).trans he
        · simpa only [neg_one_mul] using (neg_le_abs _).trans he)
  refine ⟨R,hR, ?_⟩
  intro f hf
  let g := smoothJet f hf.1
  have hg : g ∈ pdeJetCone (conePotential ν) := smoothJet_mem hf
  have hp := H 1 (Or.inl rfl) g hg
  have hm := H (-1) (Or.inr rfl) g hg
  rw [one_mul, jetDirectional_eq_fderiv hg.1] at hp
  rw [neg_one_mul, jetDirectional_eq_fderiv hg.1] at hm
  change fderiv ℝ f 0 (Real.sqrt 2 • ν) ≤
    c*(∫ y in -R..R, f (y • (Real.sqrt 2 • ν))*sech y^4) at hp
  change -fderiv ℝ f 0 (Real.sqrt 2 • ν) ≤
    c*(∫ y in -R..R, f (y • (Real.sqrt 2 • ν))*sech y^4) at hm
  exact abs_le.mpr ⟨by linarith, hp⟩

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff

lemma conePotential_positive_window_unnormalized {n : ℕ} {ν : Space n} (hν : ‖ν‖=1)
    {c : ℝ} (hc : 3/4 < c) :
    ∃ R > (0 : ℝ), ∀ f : Space n → ℝ, ContDiff ℝ ∞ f → (∀ x, 0 ≤ f x) →
      (∀ x, Laplacian.laplacian f x=conePotential ν x*f x) →
      |fderiv ℝ f 0 (Real.sqrt 2 • ν)| ≤
        c*(∫ y in -R..R, f (y • (Real.sqrt 2 • ν))*sech y^4) := by
  obtain ⟨R,hR,hbound⟩ := conePotential_positive_window hν hc
  refine ⟨R,hR,fun f hf hp hP => ?_⟩
  rcases (hp 0).eq_or_lt with hz | hz
  · have he : f = 0 := by
      funext x
      exact PositiveMaximum.nonnegative_supersolution_eq_zero (smooth_C2 hf) hp
        (fun y => by rw [hP y]; exact mul_le_mul_of_nonneg_right (conePotential_bounds ν y).2 (hp y)) hz.symm x
    simp [he]
  · have H := hbound _ (positiveLinearCone_normalize hf hp hP hz)
    rw [fderiv_const_mul (hf.differentiable (by simp) 0)] at H
    simp only [smul_apply,smul_eq_mul,abs_mul,abs_inv,abs_of_pos hz] at H
    have he : (fun y : ℝ => (f 0)⁻¹*f (y • (Real.sqrt 2 • ν))*sech y^4) =
        fun y => (f 0)⁻¹*(f (y • (Real.sqrt 2 • ν))*sech y^4) := by funext y; ring
    rw [he,intervalIntegral.integral_const_mul] at H
    exact (mul_le_mul_iff_right₀ (inv_pos.mpr hz)).mp (by nlinarith [H])

lemma even_normal_derivative_zero {n : ℕ} {ν : Space n} (hν : ‖ν‖=1)
    {E : Space n → ℝ} (hE : Differentiable ℝ E)
    (heven : ∀ x, E (normalReflection ν x)=E x) : fderiv ℝ E 0 ν=0 := by
  have hd : HasDerivAt (fun t : ℝ => E (t • ν)) (fderiv ℝ E 0 ν) 0 := by
    simpa only [zero_smul,Function.comp_def,id_eq,one_smul] using
      (hE (0 • ν)).hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_id (0:ℝ)).smul_const ν)
  have hn : HasDerivAt (fun t : ℝ => E ((-t) • ν)) (-fderiv ℝ E 0 ν) 0 := by
    simpa only [neg_zero,Function.comp_def,Pi.neg_apply,id_eq,mul_neg_one] using (show HasDerivAt (fun t : ℝ => E (t • ν)) (fderiv ℝ E 0 ν) ((-id) 0) from by simpa using hd).comp 0 ((hasDerivAt_id (0:ℝ)).neg)
  have he : (fun t : ℝ => E ((-t) • ν)) = fun t => E (t • ν) := by
    funext t
    have hr : normalReflection ν (t • ν)=(-t) • ν := by
      rw [normalReflection_apply hν,real_inner_smul_right,real_inner_self_eq_norm_sq,hν]
      simp only [one_pow,mul_one]
      module
    rw [← hr,heven]
  rw [he] at hn
  have H := hd.unique hn
  linarith

theorem SmallDefectConverges.positive_window {n : ℕ} {ν : Space n} (hν : ‖ν‖=1)
    {c : ℝ} (hc : 3/4<c) :
    ∃ R > (0 : ℝ), ∀ {v : ℕ → Space n → ℝ} {g : SmallDefectIndex n → Space n → ℝ},
      SmallDefectConverges v g → (∀ j, v j ∈ positiveDefectClass n) →
      (∀ j, v j 0=0) → Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0) →
      (∀ j, gradient (inverseProfile (v j)) 0 = Real.sqrt (1-diffuseDefect (v j) 0) • ν) →
      let F := fun x => profileWeight (inner ℝ ν x)*g (some none) x
      |fderiv ℝ F 0 (Real.sqrt 2 • ν)| ≤
        c*(∫ y in -R..R, F (y • (Real.sqrt 2 • ν))*sech y^4) := by
  obtain ⟨R,hR,hbound⟩ := conePotential_positive_window_unnormalized hν hc
  refine ⟨R,hR,?_⟩
  intro v g hg hv h0 he horient
  dsimp only
  let F := fun x => profileWeight (inner ℝ ν x)*g (some none) x
  have hF : ContDiff ℝ ∞ F :=
    (profileWeight_contDiff.comp (innerSL ℝ ν).contDiff).mul (hg.1 (some none))
  obtain ⟨E,hE,hEp,hEF,hEq,hEven⟩ := hg.even_source_removed hv h0 he hν horient
  let H := fun x => F x-E x
  have hH : ContDiff ℝ ∞ H := hF.sub hE
  have hHp (x) : 0 ≤ H x := sub_nonneg.mpr (hEF x)
  have hP (x) : Laplacian.laplacian H x=conePotential ν x*H x := by
    rw [laplacian_fun_sub (smooth_C2 hF) (smooth_C2 hE)]
    have h := hg.conjugated_equation hv h0 he hν horient x
    have h' := hEq x
    change -Laplacian.laplacian F x+(2-profileWeight (inner ℝ ν x))*F x=_ at h
    dsimp only [H,conePotential,profileWeight,profile] at *
    nlinarith [h,h']
  have HH := hbound H hH hHp hP
  have hdE : fderiv ℝ E 0 (Real.sqrt 2 • ν)=0 := by
    rw [map_smul,even_normal_derivative_zero hν (hE.differentiable (by simp)) hEven,smul_zero]
  have hd : fderiv ℝ H 0 (Real.sqrt 2 • ν)=fderiv ℝ F 0 (Real.sqrt 2 • ν) := by
    rw [fderiv_fun_sub (hF.differentiable (by simp) 0) (hE.differentiable (by simp) 0)]
    simp only [sub_apply,hdE,sub_zero]
  rw [hd] at HH
  apply HH.trans
  apply mul_le_mul_of_nonneg_left _ (by linarith [hc])
  apply intervalIntegral.integral_mono_on (by linarith [hR])
    (((hH.continuous.comp (continuous_id.smul continuous_const)).mul (contDiff_sech.continuous.pow 4)).intervalIntegrable _ _)
    (((hF.continuous.comp (continuous_id.smul continuous_const)).mul (contDiff_sech.continuous.pow 4)).intervalIntegrable _ _)
  intro y hy
  change (F (y • (Real.sqrt 2 • ν))-E (y • (Real.sqrt 2 • ν)))*sech y^4 ≤ F (y • (Real.sqrt 2 • ν))*sech y^4
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith [hEp (y • (Real.sqrt 2 • ν))]

def diffuseNormal {n : ℕ} (v : Space n → ℝ) (x : Space n) : Space n :=
  ‖gradient (inverseProfile v) x‖⁻¹ • gradient (inverseProfile v) x

def diffuseMeanCurvature {n : ℕ} (v : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, coordDeriv (fun z => inner ℝ (diffuseNormal v z)
    (EuclideanSpace.basisFun (Fin n) ℝ i)) i x

lemma diffuseNormal_component {n : ℕ} (v : Space n → ℝ) (i : Fin n) (x : Space n) :
    inner ℝ (diffuseNormal v x) (EuclideanSpace.basisFun (Fin n) ℝ i) =
      (Real.sqrt (1-diffuseDefect v x))⁻¹*coordDeriv (inverseProfile v) i x := by
  simp only [diffuseNormal,real_inner_smul_left,inner_gradient_left,diffuseDefect,
    sub_sub_cancel,Real.sqrt_sq (norm_nonneg _)]
  rfl

lemma diffuseNormal_unit {n : ℕ} {v : Space n → ℝ} {x : Space n}
    (h : diffuseDefect v x<1) : ‖diffuseNormal v x‖=1 := by
  have hp : ‖gradient (inverseProfile v) x‖ ≠ 0 := by
    intro hh
    simp [diffuseDefect,hh] at h
  rw [diffuseNormal,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ hp]

lemma inverseNormalScale_derivative {n : ℕ} {v : Space n → ℝ}
    (hv : v ∈ positiveDefectClass n) {x : Space n} (hx : diffuseDefect v x<1) :
    HasFDerivAt (fun z => (Real.sqrt (1-diffuseDefect v z))⁻¹)
      ((2*(Real.sqrt (1-diffuseDefect v x))^3)⁻¹ • fderiv ℝ (diffuseDefect v) x) x := by
  let r := Real.sqrt (1-diffuseDefect v x)
  have hr : 0<r := Real.sqrt_pos.mpr (sub_pos.mpr hx)
  have hd := ((diffuseDefect_smooth hv.1 hv.2.1).differentiable (by simp) x).hasFDerivAt
  have hs := (Real.hasDerivAt_sqrt (ne_of_gt (sub_pos.mpr hx))).comp_hasFDerivAt x (hd.const_sub 1)
  have H := (hasDerivAt_inv hr.ne').comp_hasFDerivAt x hs
  have hh : -(r^2)⁻¹ • (1 / (2 * Real.sqrt (1-diffuseDefect v x))) •
      -fderiv ℝ (diffuseDefect v) x =
      (2*(Real.sqrt (1-diffuseDefect v x))^3)⁻¹ • fderiv ℝ (diffuseDefect v) x := by
    ext y
    simp only [smul_apply,smul_eq_mul,neg_apply,div_eq_mul_inv]
    dsimp only [r] at hr ⊢
    field_simp [hr.ne']
  rw [hh] at H
  exact H

lemma diffuseMeanCurvature_zero {n : ℕ} {v : Space n → ℝ}
    (hv : v ∈ positiveDefectClass n) {x : Space n} (h0 : v x=0)
    (hx : diffuseDefect v x<1) :
    diffuseMeanCurvature v x =
      fderiv ℝ (diffuseDefect v) x (diffuseNormal v x) /
        (2*(1-diffuseDefect v x)) := by
  let U := inverseProfile v
  let D := diffuseDefect v
  let r := Real.sqrt (1-D x)
  have hU : ContDiff ℝ ∞ U := inverseProfile_smooth hv.1 hv.2.1
  have hr : 0<r := Real.sqrt_pos.mpr (sub_pos.mpr hx)
  have hr2 : r^2=1-D x := Real.sq_sqrt (sub_pos.mpr hx).le
  have hscale := inverseNormalScale_derivative hv hx
  have he (i : Fin n) : coordDeriv (fun z => inner ℝ (diffuseNormal v z)
        (EuclideanSpace.basisFun (Fin n) ℝ i)) i x =
      r⁻¹*coordDeriv (coordDeriv U i) i x + (2*r^3)⁻¹*coordDeriv D i x*coordDeriv U i x := by
    rw [show (fun z => inner ℝ (diffuseNormal v z) (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      fun z => (Real.sqrt (1-D z))⁻¹*coordDeriv U i z from funext (diffuseNormal_component v i)]
    change fderiv ℝ (fun z => (Real.sqrt (1-D z))⁻¹*coordDeriv U i z) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) = _
    rw [fderiv_fun_mul hscale.differentiableAt ((coordDeriv_smooth hU i).differentiable (by simp) x),hscale.fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul]
    change r⁻¹ * coordDeriv (coordDeriv U i) i x + coordDeriv U i x *
      ((2*r^3)⁻¹ * coordDeriv D i x) = _
    ring
  have hl : Laplacian.laplacian U x=0 := by
    change Laplacian.laplacian (inverseProfile v) x=0
    rw [inverseProfile_laplacian_eq (smooth_C2 hv.1) hv.2.1 hv.2.2.1,h0]
    ring
  unfold diffuseMeanCurvature
  simp_rw [he]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← laplacian_eq_sum_coordDeriv (smooth_C2 hU),hl,mul_zero,zero_add]
  have hsum : (∑ i : Fin n, coordDeriv D i x*coordDeriv U i x) =
      fderiv ℝ D x (gradient U x) := by
    rw [← inner_gradient_eq_sum,inner_gradient_left]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum,hsum]
  have hn : diffuseNormal v x=r⁻¹ • gradient U x := by
    dsimp [diffuseNormal,r,D,diffuseDefect]
    rw [sub_sub_cancel,Real.sqrt_sq (norm_nonneg _)]
  rw [hn,map_smul]
  simp only [smul_eq_mul]
  rw [← hr2]
  field_simp [hr.ne']
  ring

lemma fderiv_eq_basis_sum {n : ℕ} (f : Space n → ℝ) (x w : Space n) :
    fderiv ℝ f x w = ∑ i : Fin n, coordDeriv f i x *
      inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i) w := by
  rw [← inner_gradient_left]
  change inner ℝ (gradient f x) w = ∑ i : Fin n,
    fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)*
      inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i) w
  simpa only [inner_gradient_left] using
    ((EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner (gradient f x) w).symm

lemma SmallDefectConverges.directional_D {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (x w : Space n) :
    Tendsto (fun j => (diffuseDefect (v j) 0)⁻¹ * fderiv ℝ (diffuseDefect (v j)) x w)
      atTop (𝓝 (fderiv ℝ (g (some none)) x w)) := by
  simp_rw [fderiv_eq_basis_sum,Finset.mul_sum,← mul_assoc]
  exact tendsto_finsetSum _ (fun i _ => (hg.at_D [i] x).mul_const _)

lemma conjugated_derivative_zero {n : ℕ} {d : Space n → ℝ}
    (hd : Differentiable ℝ d) (ν w : Space n) :
    fderiv ℝ (fun x => profileWeight (inner ℝ ν x)*d x) 0 w =
      fderiv ℝ d 0 w := by
  have hG := (profileWeight_hasDerivAt (inner ℝ ν (0 : Space n))).comp_hasFDerivAt 0
    (innerSL ℝ ν).hasFDerivAt
  change HasFDerivAt (fun z => profileWeight (inner ℝ ν z)) _ _ at hG
  rw [fderiv_fun_mul hG.differentiableAt (hd 0),hG.fderiv]
  simp [profileWeight,profile]

theorem SmallDefectConverges.mean_limit {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n) (h0 : ∀ j, v j 0=0)
    (he : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0)) {ν : Space n}
    (hν : ‖ν‖=1)
    (horient : ∀ j, gradient (inverseProfile (v j)) 0 =
      Real.sqrt (1-diffuseDefect (v j) 0) • ν) :
    Tendsto (fun j => diffuseMeanCurvature (v j) 0 / diffuseDefect (v j) 0)
      atTop (𝓝 ((1/2 : ℝ)*fderiv ℝ (fun x => profileWeight (inner ℝ ν x)*g (some none) x) 0 ν)) := by
  have hev : ∀ᶠ j in atTop, diffuseDefect (v j) 0<1 :=
    he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))
  have hden : Tendsto (fun j => 2*(1-diffuseDefect (v j) 0)) atTop (𝓝 (2 : ℝ)) := by
    simpa only [sub_zero,mul_one] using ((tendsto_const_nhds (x := (1 : ℝ))).sub he).const_mul 2
  have H := (hg.directional_D 0 ν).div hden (by norm_num)
  rw [conjugated_derivative_zero ((hg.1 (some none)).differentiable (by simp))]
  rw [show (1/2 : ℝ)*fderiv ℝ (g (some none)) 0 ν =
    fderiv ℝ (g (some none)) 0 ν / 2 by ring]
  apply H.congr'
  filter_upwards [hev] with j hj
  have hr : 0 < Real.sqrt (1-diffuseDefect (v j) 0) := Real.sqrt_pos.mpr (sub_pos.mpr hj)
  have hn : diffuseNormal (v j) 0 = ν := by
    rw [diffuseNormal,horient j,norm_smul,hν,Real.norm_eq_abs,abs_of_pos hr,mul_one,
      smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
  rw [diffuseMeanCurvature_zero (hv j) (h0 j) hj,hn]
  simp only [Pi.div_apply]
  ring

lemma profile_uniformContinuous : UniformContinuous profile := by
  apply (lipschitzWith_of_nnnorm_deriv_le (C := 1)
    (profile_contDiff.differentiable (by simp)) ?_).uniformContinuous
  intro s
  rw [← NNReal.coe_le_coe,coe_nnnorm,NNReal.coe_one,(profile_hasDerivAt s).deriv,
    Real.norm_eq_abs,abs_of_nonneg (div_nonneg (profileWeight_pos s).le (Real.sqrt_nonneg _))]
  have hs : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  apply (div_le_one (Real.sqrt_pos.mpr (by norm_num))).mpr
  exact (by dsimp [profileWeight]; nlinarith [sq_nonneg (profile s)] : profileWeight s ≤ 1).trans hs

lemma SmallDefectConverges.v_locallyUniform {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n) :
    TendstoLocallyUniformly v (fun x => profile (g none x)) atTop := by
  have hU : TendstoLocallyUniformly (fun j => inverseProfile (v j)) (g none) atTop := by
    convert hg.2 none [] using 1
    · funext j x
      simp [normalizedSmallJet,smallDefectScale,smallDefectEntry,coordinateJet]
    · rfl
  have H := profile_uniformContinuous.comp_tendstoLocallyUniformly hU
  have he : (fun j => profile ∘ inverseProfile (v j)) = v := by
    funext j x
    exact profile_inverseProfile (hv j).2.1 x
  rwa [he] at H

lemma SmallDefectConverges.normalized_mass_locallyUniform {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n) :
    TendstoLocallyUniformly
      (fun j x => (diffuseDefect (v j) 0)⁻¹ * (defectWeight (v j) x)^3 * diffuseDefect (v j) x)
      (fun x => profileWeight (g none x)^3*g (some none) x) atTop := by
  have hvu := hg.v_locallyUniform hv
  have hvc : Continuous (fun x => profile (g none x)) := profile_contDiff.continuous.comp (hg.1 none).continuous
  have hq : TendstoLocallyUniformly (fun j => defectWeight (v j)) (fun x => profileWeight (g none x)) atTop := by
    have h1 : TendstoLocallyUniformly (fun _ : ℕ => fun _ : Space n => (1 : ℝ)) (fun _ => 1) atTop :=
      tendsto_const_nhds.tendstoUniformly_const.tendstoLocallyUniformly
    have H := h1.sub (hvu.mul₀ hvu hvc hvc)
    convert H using 1 <;> ext <;> simp [defectWeight,profileWeight,pow_two]
  have hqc : Continuous (fun x => profileWeight (g none x)) := profileWeight_contDiff.continuous.comp (hg.1 none).continuous
  have hq3 := (hq.mul₀ hq hqc hqc).mul₀ hq (hqc.mul hqc) hqc
  have hD : TendstoLocallyUniformly (fun j x => (diffuseDefect (v j) 0)⁻¹*diffuseDefect (v j) x)
      (g (some none)) atTop := hg.2 (some none) []
  have H := hq3.mul₀ hD ((hqc.mul hqc).mul hqc) (hg.1 (some none)).continuous
  convert H using 1 <;> ext <;> simp only [Pi.mul_apply] <;> ring

noncomputable def reducedNormalMass {n : ℕ} (v : Space n → ℝ) (ν : Space n) (R : ℝ) : ℝ :=
  ∫ y in -R..R, (defectWeight v (y • (Real.sqrt 2 • ν)))^3 * diffuseDefect v (y • (Real.sqrt 2 • ν))

lemma SmallDefectConverges.normal_mass_limit {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n) (ν : Space n) (R : ℝ) :
    Tendsto (fun j => reducedNormalMass (v j) ν R / diffuseDefect (v j) 0) atTop
      (𝓝 (∫ y in -R..R, profileWeight (g none (y • (Real.sqrt 2 • ν)))^3*g (some none) (y • (Real.sqrt 2 • ν)))) := by
  have H := (hg.normalized_mass_locallyUniform hv).comp (fun y : ℝ => y • (Real.sqrt 2 • ν))
    (continuous_id.smul continuous_const)
  have hu := tendstoLocallyUniformly_iff_forall_isCompact.mp H (Set.uIcc (-R) R) isCompact_uIcc
  have hi := hu.tendsto_intervalIntegral_of_continuousOn (μ := MeasureTheory.volume)
    (Filter.Eventually.of_forall (fun j =>
      (((continuous_const.mul (((show ContDiff ℝ ∞ (defectWeight (v j)) from contDiff_const.sub ((hv j).1.pow 2)).continuous.comp
        (continuous_id.smul continuous_const)).pow 3)).mul
        ((diffuseDefect_smooth (hv j).1 (hv j).2.1).continuous.comp
          (continuous_id.smul continuous_const))).continuousOn)))
  convert hi using 1
  · funext j
    change reducedNormalMass (v j) ν R / diffuseDefect (v j) 0 =
      ∫ y in -R..R, (diffuseDefect (v j) 0)⁻¹ * (defectWeight (v j) (y • (Real.sqrt 2 • ν)))^3 * diffuseDefect (v j) (y • (Real.sqrt 2 • ν))
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul]
    exact div_eq_inv_mul _ _
  · rfl

lemma profileWeight_normal {n : ℕ} {ν : Space n} (hν : ‖ν‖=1) (y : ℝ) :
    profileWeight (inner ℝ ν (y • (Real.sqrt 2 • ν)))=sech y^2 := by
  rw [real_inner_smul_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hν]
  simp only [one_pow,mul_one]
  dsimp only [profileWeight,profile]
  rw [mul_div_cancel_right₀ _ (Real.sqrt_ne_zero'.mpr (by norm_num))]
  linarith [sech_sq_tanh y]

end DeGiorgi
end

end OAI
