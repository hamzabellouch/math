import OAI.Analysis.AllenCahn.PositiveWindows

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff

lemma SmallDefectConverges.mass_positive {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n) (ν : Space n) {R : ℝ} (hR : 0<R) :
    0 < ∫ y in -R..R, profileWeight (g none (y • (Real.sqrt 2 • ν)))^3*
      g (some none) (y • (Real.sqrt 2 • ν)) := by
  have hc : Continuous (fun y : ℝ => profileWeight (g none (y • (Real.sqrt 2 • ν)))^3*
      g (some none) (y • (Real.sqrt 2 • ν))) :=
    (((profileWeight_contDiff.continuous.comp (hg.1 none).continuous).comp
      (continuous_id.smul continuous_const)).pow 3).mul
      ((hg.1 (some none)).continuous.comp (continuous_id.smul continuous_const))
  have hp (y : ℝ) : 0 < profileWeight (g none (y • (Real.sqrt 2 • ν)))^3*
      g (some none) (y • (Real.sqrt 2 • ν)) :=
    mul_pos (pow_pos (profileWeight_pos _) _) ((hg.positive hv).2 _)
  exact intervalIntegral.integral_pos (by linarith) hc.continuousOn
    (fun y _ => (hp y).le) ⟨0,⟨by linarith,by linarith⟩,hp 0⟩

theorem small_defect_mean_window_normalized {n : ℕ} {ν : Space n} (hν : ‖ν‖=1)
    {c : ℝ} (hc : 3/4<c) :
    ∃ R > (0 : ℝ), ∃ δ ∈ Set.Ioc (0 : ℝ) (1/2),
      ∀ v ∈ positiveDefectClass n, v 0=0 → diffuseDefect v 0<δ →
      gradient (inverseProfile v) 0=Real.sqrt (1-diffuseDefect v 0) • ν →
      |2*Real.sqrt 2*diffuseMeanCurvature v 0| ≤ c*reducedNormalMass v ν R := by
  obtain ⟨c₀,hc₀,hc₀c⟩ := exists_between hc
  obtain ⟨R,hR,hbound⟩ := SmallDefectConverges.positive_window hν hc₀
  refine ⟨R,hR,?_⟩
  by_contra! hbad
  have hseq (j : ℕ) : ∃ v ∈ positiveDefectClass n, v 0=0 ∧
      diffuseDefect v 0 < min (1/2) (1/(j+1 : ℝ)) ∧
      gradient (inverseProfile v) 0=Real.sqrt (1-diffuseDefect v 0) • ν ∧
      c*reducedNormalMass v ν R < |2*Real.sqrt 2*diffuseMeanCurvature v 0| := by
    exact hbad _ ⟨lt_min (by norm_num) (by positivity),min_le_left _ _⟩
  choose v hv h0 he horient hviol using hseq
  have he0 : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0) :=
    squeeze_zero (fun j => ((hv j).2.2.2 0).le)
      (fun j => (he j).le.trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨a,g,ha,hg⟩ := smallDefect_compactness hv h0
  have hv' (j) := hv (a j)
  have h0' (j) := h0 (a j)
  have he' := he0.comp ha.tendsto_atTop
  have horient' (j) := horient (a j)
  let F := fun x => profileWeight (inner ℝ ν x)*g (some none) x
  let M := ∫ y in -R..R, profileWeight (g none (y • (Real.sqrt 2 • ν)))^3*g (some none) (y • (Real.sqrt 2 • ν))
  have hM : 0<M := hg.mass_positive hv' ν hR
  have hFp : |fderiv ℝ F 0 (Real.sqrt 2 • ν)| ≤ c₀*M := by
    have H := hbound hg hv' h0' he' horient'
    have hmass : (∫ y in -R..R, F (y • (Real.sqrt 2 • ν))*sech y^4)=M := by
      unfold M
      rw [hg.profile_limit hv' h0' he' horient']
      apply intervalIntegral.integral_congr
      intro y hy
      dsimp only [F]
      rw [profileWeight_normal hν]
      ring
    simpa only [← hmass] using H
  have hm := hg.normal_mass_limit hv' ν R
  have hh := ((hg.mean_limit hv' h0' he' hν horient').const_mul (2*Real.sqrt 2)).abs
  have hh' : Tendsto (fun j => |2*Real.sqrt 2*diffuseMeanCurvature (v (a j)) 0| /
      diffuseDefect (v (a j)) 0) atTop (𝓝 |fderiv ℝ F 0 (Real.sqrt 2 • ν)|) := by
    convert hh using 1
    · funext j
      rw [← mul_div_assoc,abs_div,abs_of_pos ((hv' j).2.2.2 0)]
    · congr 2
      rw [map_smul]
      simp only [smul_eq_mul]
      dsimp only [F]
      ring
  have hrev : c*M ≤ |fderiv ℝ F 0 (Real.sqrt 2 • ν)| := by
    apply le_of_tendsto_of_tendsto (hm.const_mul c) hh'
    filter_upwards [] with j
    have H := (div_lt_div_of_pos_right (hviol (a j)) ((hv' j).2.2.2 0)).le
    simpa only [mul_div_assoc] using H
  nlinarith

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

lemma fderiv_affine_isometry {n : ℕ} {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (z : Space n) (J : Space n ≃ₗᵢ[ℝ] Space n) (x w : Space n) :
    fderiv ℝ (fun y => f (z+J y)) x w = fderiv ℝ f (z+J x) (J w) := by
  have H := (hf (z+J x)).hasFDerivAt.comp x (J.hasFDerivAt.const_add z)
  change HasFDerivAt (fun y => f (z+J y)) _ x at H
  rw [H.fderiv]
  rfl

lemma gradient_affine_isometry {n : ℕ} {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (z : Space n) (J : Space n ≃ₗᵢ[ℝ] Space n) (x : Space n) :
    gradient (fun y => f (z+J y)) x = J.symm (gradient f (z+J x)) := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_gradient_left,fderiv_affine_isometry hf,J.symm.inner_map_eq_flip,
    J.symm_symm,inner_gradient_left]

lemma diffuseDefect_affine_isometry {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (z : Space n) (J : Space n ≃ₗᵢ[ℝ] Space n) (x : Space n) :
    diffuseDefect (fun y => v (z+J y)) x = diffuseDefect v (z+J x) := by
  have he : inverseProfile (fun y => v (z+J y)) = fun y => inverseProfile v (z+J y) := rfl
  unfold diffuseDefect
  rw [he,gradient_affine_isometry ((inverseProfile_smooth hv hi).differentiable (by simp)),J.symm.norm_map]

lemma positiveDefectClass_affine_isometry {n : ℕ} {v : Space n → ℝ}
    (hv : v ∈ positiveDefectClass n) (z : Space n) (J : Space n ≃ₗᵢ[ℝ] Space n) :
    (fun y => v (z+J y)) ∈ positiveDefectClass n := by
  refine ⟨hv.1.comp (contDiff_const.add J.contDiff),fun x => hv.2.1 _,?_,?_⟩
  · intro x
    have ht : ContDiff ℝ 2 (fun t => v (z+t)) :=
      (smooth_C2 hv.1).comp (contDiff_const.add contDiff_id)
    rw [show Laplacian.laplacian (fun y => v (z+J y)) x = Laplacian.laplacian (fun t => v (z+t)) (J x) from
      PoissonSupport.DeGiorgi.laplacian_comp_isometry ht J x,
      PoissonSupport.DeGiorgi.laplacian_translate (smooth_C2 hv.1)]
    exact hv.2.2.1 _
  · intro x
    rw [diffuseDefect_affine_isometry hv.1 hv.2.1]
    exact hv.2.2.2 _

lemma diffuseNormal_affine_isometry {n : ℕ} {v : Space n → ℝ}
    (hv : v ∈ positiveDefectClass n) (z : Space n) (J : Space n ≃ₗᵢ[ℝ] Space n) (x : Space n) :
    diffuseNormal (fun y => v (z+J y)) x=J.symm (diffuseNormal v (z+J x)) := by
  have he : inverseProfile (fun y => v (z+J y)) = fun y => inverseProfile v (z+J y) := rfl
  unfold diffuseNormal
  rw [he,gradient_affine_isometry ((inverseProfile_smooth hv.1 hv.2.1).differentiable (by simp)),
    J.symm.norm_map, J.symm.map_smul]

lemma diffuseMeanCurvature_affine_isometry_zero {n : ℕ} {v : Space n → ℝ}
    (hv : v ∈ positiveDefectClass n) (z : Space n) (J : Space n ≃ₗᵢ[ℝ] Space n)
    (h0 : v z=0) (hz : diffuseDefect v z<1) :
    diffuseMeanCurvature (fun y => v (z+J y)) 0=diffuseMeanCurvature v z := by
  have hv' := positiveDefectClass_affine_isometry hv z J
  have h0' : (fun y => v (z+J y)) 0=0 := by simpa using h0
  have hD : diffuseDefect (fun y => v (z+J y)) 0=diffuseDefect v z := by
    simpa using diffuseDefect_affine_isometry hv.1 hv.2.1 z J 0
  rw [diffuseMeanCurvature_zero hv' h0' (hD ▸ hz),diffuseMeanCurvature_zero hv h0 hz,hD]
  congr 1
  rw [show diffuseDefect (fun y => v (z+J y)) = fun y => diffuseDefect v (z+J y) from
    funext (diffuseDefect_affine_isometry hv.1 hv.2.1 z J),
    fderiv_affine_isometry ((diffuseDefect_smooth hv.1 hv.2.1).differentiable (by simp)),
    diffuseNormal_affine_isometry hv,J.apply_symm_apply]
  simp

lemma gradient_eq_normal {n : ℕ} (v : Space n → ℝ) (z : Space n) :
    gradient (inverseProfile v) z=Real.sqrt (1-diffuseDefect v z) • diffuseNormal v z := by
  simp only [diffuseDefect,sub_sub_cancel,Real.sqrt_sq (norm_nonneg _),diffuseNormal,smul_smul]
  by_cases h : ‖gradient (inverseProfile v) z‖=0
  · rw [h,zero_mul,zero_smul]
    exact norm_eq_zero.mp h
  · rw [mul_inv_cancel₀ h,one_smul]

noncomputable def normalDefectMass {n : ℕ} (v : Space n → ℝ) (z : Space n) (P : ℝ) : ℝ :=
  ∫ s in -P..P, defectWeight v (z+s • diffuseNormal v z)^3 * diffuseDefect v (z+s • diffuseNormal v z)

lemma normal_mass_affine_isometry {n : ℕ} {v : Space n → ℝ}
    (hv : v ∈ positiveDefectClass n) (z : Space n) (J : Space n ≃ₗᵢ[ℝ] Space n)
    (ν : Space n) (hJ : J ν=diffuseNormal v z) (R : ℝ) :
    normalDefectMass v z (R*Real.sqrt 2) =
      Real.sqrt 2*reducedNormalMass (fun x => v (z+J x)) ν R := by
  let f := fun s : ℝ => defectWeight v (z+s • diffuseNormal v z)^3 * diffuseDefect v (z+s • diffuseNormal v z)
  have he (y : ℝ) : defectWeight (fun x => v (z+J x)) (y • (Real.sqrt 2 • ν))^3 *
    diffuseDefect (fun x => v (z+J x)) (y • (Real.sqrt 2 • ν))=f (y*Real.sqrt 2) := by
    rw [diffuseDefect_affine_isometry hv.1 hv.2.1]
    simp only [defectWeight,J.map_smul,hJ,smul_smul,f]
  have H := intervalIntegral.integral_comp_mul_right (a := -R) (b := R) f
    (Real.sqrt_ne_zero'.mpr (by norm_num) : Real.sqrt 2≠0)
  unfold reducedNormalMass
  simp_rw [he]
  rw [H]
  simp only [smul_eq_mul,neg_mul]
  change normalDefectMass v z (R*Real.sqrt 2) =
    Real.sqrt 2*((Real.sqrt 2)⁻¹ * normalDefectMass v z (R*Real.sqrt 2))
  rw [← mul_assoc,mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num)),one_mul]

theorem diffuse_mean_window_positive {n : ℕ} (hn : 0<n) {c : ℝ}
    (hc : 1/(2*Real.sqrt 2)<c) :
    ∃ P > (0 : ℝ), ∃ δ ∈ Set.Ioc (0 : ℝ) (1/2),
      ∀ v ∈ positiveDefectClass n, ∀ z : Space n,
      v z=0 → diffuseDefect v z<δ →
      |diffuseMeanCurvature v z| ≤ (c/(4*Real.sqrt 2/3))*normalDefectMass v z P := by
  let ν : Space n := EuclideanSpace.basisFun (Fin n) ℝ ⟨0,hn⟩
  have hν : ‖ν‖=1 := by simp [ν]
  let c' := (3*Real.sqrt 2/2)*c
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2^2=2 := Real.sq_sqrt (by norm_num)
  have hc' : 3/4<c' := by
    have HH := (div_lt_iff₀ (show 0<2*Real.sqrt 2 by positivity)).mp hc
    dsimp only [c']
    nlinarith
  obtain ⟨R,hR,δ,hδ,hbound⟩ := small_defect_mean_window_normalized hν hc'
  refine ⟨R*Real.sqrt 2,mul_pos hR hs,δ,hδ,?_⟩
  intro v hv z h0 hz
  have hz1 : diffuseDefect v z<1 := lt_of_lt_of_le hz (hδ.2.trans (by norm_num))
  let J : Space n ≃ₗᵢ[ℝ] Space n := (Submodule.span ℝ {ν-diffuseNormal v z})ᗮ.reflection
  have hJ : J ν=diffuseNormal v z := Submodule.reflection_sub (hν.trans (diffuseNormal_unit hz1).symm)
  let w := fun x => v (z+J x)
  have hw : w ∈ positiveDefectClass n := positiveDefectClass_affine_isometry hv z J
  have hw0 : w 0=0 := by simpa [w] using h0
  have hD : diffuseDefect w 0=diffuseDefect v z := by
    simpa [w] using diffuseDefect_affine_isometry hv.1 hv.2.1 z J 0
  have horient : gradient (inverseProfile w) 0=Real.sqrt (1-diffuseDefect w 0) • ν := by
    change gradient (fun x => inverseProfile v (z+J x)) 0=_
    rw [gradient_affine_isometry ((inverseProfile_smooth hv.1 hv.2.1).differentiable (by simp)),
      J.map_zero,add_zero,gradient_eq_normal v z,J.symm.map_smul,← hJ,J.symm_apply_apply,hD]
  have H := hbound w hw hw0 (hD ▸ hz) horient
  have hmean : diffuseMeanCurvature w 0=diffuseMeanCurvature v z :=
    diffuseMeanCurvature_affine_isometry_zero hv z J h0 hz1
  rw [hmean,abs_mul,abs_of_pos (show 0<2*Real.sqrt 2 by positivity)] at H
  rw [normal_mass_affine_isometry hv z J ν hJ R]
  have hcoef : c/(4*Real.sqrt 2/3)*Real.sqrt 2=c'/(2*Real.sqrt 2) := by
    dsimp only [c']
    field_simp [hs.ne']
    nlinarith
  rw [← mul_assoc,hcoef]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show 0<2*Real.sqrt 2 by positivity)).mpr
  simpa only [_root_.mul_comm] using H

lemma normalDefectMass_mono {n : ℕ} {v : Space n → ℝ}
    (hv : v ∈ positiveDefectClass n) (z : Space n) {P P' : ℝ} (hP : 0≤P) (hPP' : P≤P') :
    normalDefectMass v z P≤normalDefectMass v z P' := by
  have hf : Continuous (fun s : ℝ => defectWeight v (z+s • diffuseNormal v z)^3 *
      diffuseDefect v (z+s • diffuseNormal v z)) :=
    (((contDiff_const.sub (hv.1.pow 2)).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).pow 3).mul
      ((diffuseDefect_smooth hv.1 hv.2.1).continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const)))
  apply intervalIntegral.integral_mono_interval (neg_le_neg hPP') (by linarith) hPP' _ (hf.intervalIntegrable _ _)
  exact MeasureTheory.ae_of_all _ (fun s => mul_nonneg
    (pow_nonneg (by dsimp [defectWeight]; nlinarith [(hv.2.1 (z+s • diffuseNormal v z)).1,
      (hv.2.1 (z+s • diffuseNormal v z)).2]) _) (hv.2.2.2 _).le)

end DeGiorgi
end

end OAI
