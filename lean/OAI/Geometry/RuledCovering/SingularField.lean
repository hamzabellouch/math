import OAI.Geometry.RuledCovering.Nilpotent

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singular_parameter_bounds {p gamma : ℝ} (hp : 1 < p)
    (hp' : p < (Real.sqrt 51-5)/2) (hg : 1 < gamma) (hg' : gamma < 1/(2-p)) :
    p < 2 ∧ 0 < 1+gamma*(p-2) ∧ 0 < 2*gamma-2 ∧ singularCoefficient p < 0 := by
  have hs : (Real.sqrt 51)^2 = (51:ℝ) := Real.sq_sqrt (by norm_num)
  have hsn := Real.sqrt_nonneg (51:ℝ)
  have hs9 : Real.sqrt 51 < 9 := by nlinarith
  have hp2 : p < 2 := by linarith
  have hgam : gamma*(2-p) < 1 := (lt_div_iff₀ (sub_pos.mpr hp2)).mp hg'
  have hroot : 2*p+5 < Real.sqrt 51 := by linarith
  have hnum : 2*p^2+10*p-13 < 0 := by nlinarith
  refine ⟨hp2, by nlinarith, by linarith, ?_⟩
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hnum) (by linarith)

lemma singularField_contDiffAt (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (singularField p) z := by
  apply contDiffAt_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun b : Plane => ((1/2:ℝ)/2)*(b 1/(1/2))^(p-1)*
        (p+(2-p)*(b 0/b 1)^2)) z
    have h1 : ContDiffAt ℝ ∞ (fun b : Plane => b 1/(1/2:ℝ)) z := by fun_prop
    have hpow := h1.rpow_const_of_ne (p := p-1) (by positivity)
    exact (contDiffAt_const.mul hpow).mul
      (contDiffAt_const.add (contDiffAt_const.mul (((by fun_prop :
        ContDiffAt ℝ ∞ (fun b : Plane => b 0) z).div (by fun_prop) hz.ne').pow 2)))
  · change ContDiffAt ℝ ∞ (fun b : Plane => (b 1/(1/2:ℝ))^(p-2)*b 0) z
    have h1 : ContDiffAt ℝ ∞ (fun b : Plane => b 1/(1/2:ℝ)) z := by fun_prop
    exact (h1.rpow_const_of_ne (p := p-2) (by positivity)).mul (by fun_prop)

lemma singularField_contDiffOn (p : ℝ) :
    ContDiffOn ℝ ∞ (singularField p) {z : Plane | 0 < z 1} :=
  fun _ hz => (singularField_contDiffAt p hz).contDiffWithinAt

lemma singularField_smul (p : ℝ) {r : ℝ} (hr : 0 < r) {z : Plane} (hz : 0 < z 1) :
    singularField p (r • z) = r^(p-1) • singularField p z := by
  have he : (r*z 1)/(1/2:ℝ) = r*(z 1/(1/2)) := by ring
  have hpow : r^(p-1) = r^(p-2)*r := by
    rw [show p-1 = p-2+1 by ring,Real.rpow_add_one hr.ne']
  ext i
  fin_cases i
  · change ((1/2:ℝ)/2)*((r*z 1)/(1/2))^(p-1)*(p+(2-p)*(r*z 0/(r*z 1))^2) =
      r^(p-1)*(((1/2:ℝ)/2)*(z 1/(1/2))^(p-1)*(p+(2-p)*(z 0/z 1)^2))
    rw [he,Real.mul_rpow hr.le (by positivity),mul_div_mul_left _ _ hr.ne']
    ring
  · change ((r*z 1)/(1/2:ℝ))^(p-2)*(r*z 0) = r^(p-1)*((z 1/(1/2))^(p-2)*z 0)
    rw [he,Real.mul_rpow hr.le (by positivity),hpow]
    ring

lemma singularField_fderiv_smul (p : ℝ) {r : ℝ} (hr : 0 < r) {z : Plane} (hz : 0 < z 1) :
    fderiv ℝ (singularField p) (r • z) = r^(p-2) • fderiv ℝ (singularField p) z := by
  have he : (fun w : Plane => singularField p (r • w)) =ᶠ[𝓝 z]
      (fun w : Plane => r^(p-1) • singularField p w) := by
    filter_upwards [(isOpen_lt continuous_const (by fun_prop : Continuous (fun w : Plane => w 1))).mem_nhds hz]
      with w hw
    exact singularField_smul p hr hw
  have hd := (singularField_contDiffAt p hz).differentiableAt (by norm_num)
  have he' := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp_smul r, fderiv_fun_const_smul hd] at he'
  have hp : r^(p-1) = r*r^(p-2) := by
    rw [show p-1 = p-2+1 by ring,Real.rpow_add_one hr.ne']
    ring
  rw [hp,mul_smul] at he'
  exact (smul_right_injective (Plane →L[ℝ] Plane) hr.ne') he'

lemma singularField_level (p b : ℝ) :
    singularField p (vec2 b (1/2)) = vec2 (p/4+(2-p)*b^2) b := by
  ext i
  fin_cases i <;> simp [singularField,vec2]; ring

lemma singularField_wall (p : ℝ) {b r : ℝ} (hr : 0 < r) :
    singularField p (vec2 b r) 1 + singularField p (vec2 b r) 0 =
      (r+b)/2*(r/(1/2:ℝ))^(p-2)*((2-p)*b/r+p) ∧
    singularField p (vec2 b r) 1 - singularField p (vec2 b r) 0 =
      (r-b)/2*(r/(1/2:ℝ))^(p-2)*((2-p)*b/r-p) := by
  have hp : (r/(1/2:ℝ))^(p-1) = (r/(1/2:ℝ))^(p-2)*(r/(1/2)) := by
    rw [show p-1 = p-2+1 by ring,Real.rpow_add_one (by positivity : r/(1/2:ℝ)≠0)]
  simp only [singularField,vec2_apply_one,vec2_apply_zero,hp]
  constructor <;> field_simp <;> ring

def matrixCLM (a b c d : ℝ) : Plane →L[ℝ] Plane :=
  (a • EuclideanSpace.proj 0 + b • EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).smulRight (vec2 1 0) +
  (c • EuclideanSpace.proj 0 + d • EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).smulRight (vec2 0 1)

@[simp] lemma matrixCLM_apply (a b c d : ℝ) (z : Plane) :
    matrixCLM a b c d z = vec2 (a*z 0+b*z 1) (c*z 0+d*z 1) := by
  ext i
  fin_cases i <;> simp [matrixCLM,vec2]

lemma hasFDerivAt_vec2 {f g : Plane → ℝ} {f' g' : Plane →L[ℝ] ℝ} {z : Plane}
    (hf : HasFDerivAt f f' z) (hg : HasFDerivAt g g' z) :
    HasFDerivAt (fun w => vec2 (f w) (g w))
      (f'.smulRight (vec2 1 0) + g'.smulRight (vec2 0 1)) z := by
  have he : (fun w => vec2 (f w) (g w)) =
      (fun w => f w • vec2 1 0 + g w • vec2 0 1) := by
    funext w
    ext i
    fin_cases i <;> simp [vec2]
  rw [he]
  exact (hf.smul_const (vec2 1 0)).add (hg.smul_const (vec2 0 1))

lemma singularField_fderiv (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    fderiv ℝ (singularField p) z =
      matrixCLM ((2-p)*(z 1/(1/2:ℝ))^(p-2)*(z 0/z 1))
        ((z 1/(1/2:ℝ))^(p-2)/2*(p*(p-1)+(2-p)*(p-3)*(z 0/z 1)^2))
        ((z 1/(1/2:ℝ))^(p-2)) ((p-2)*(z 1/(1/2:ℝ))^(p-2)*(z 0/z 1)) := by
  let b : Plane →L[ℝ] ℝ := EuclideanSpace.proj 0
  let r : Plane →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hb := b.hasFDerivAt (x := z)
  have hr := r.hasFDerivAt (x := z)
  have hri := (hasDerivAt_inv hz.ne').comp_hasFDerivAt z hr
  have hquot := hb.mul hri
  have hscale := hr.const_mul 2
  have hpow1 := hscale.rpow_const (p := p-1) (Or.inl (by change 2*z 1 ≠ 0; positivity))
  have hpow2 := hscale.rpow_const (p := p-2) (Or.inl (by change 2*z 1 ≠ 0; positivity))
  have hP := (hpow1.const_mul ((1/2:ℝ)/2)).mul
    (((hquot.pow 2).const_mul (2-p)).const_add p)
  have hQ := hpow2.mul hb
  have hf := (hasFDerivAt_vec2 hP hQ).fderiv
  have he : (fun w : Plane => vec2 (((1/2:ℝ)/2)*(2*r w)^(p-1)*
      (p+(2-p)*(b w*(r w)⁻¹)^2)) ((2*r w)^(p-2)*b w)) = singularField p := by
    funext w
    ext i
    fin_cases i <;> simp [singularField,vec2,b,r,div_eq_mul_inv,mul_comm]
  change fderiv ℝ (fun w : Plane => vec2 (((1/2:ℝ)/2)*(2*r w)^(p-1)*
      (p+(2-p)*(b w*(r w)⁻¹)^2)) ((2*r w)^(p-2)*b w)) z = _ at hf
  rw [he] at hf
  rw [hf]
  have h2 : 0 < 2*z 1 := by positivity
  have hp1 : (2*z 1)^(p-1-1) = (2*z 1)^(p-2) := by congr 1; ring
  have hp2 : (2*z 1)^(p-2-1) = (2*z 1)^(p-2)/(2*z 1) := by
    rw [Real.rpow_sub_one h2.ne']
  have hp3 : (2*z 1)^(p-1) = (2*z 1)^(p-2)*(2*z 1) := by
    rw [show p-1 = p-2+1 by ring,Real.rpow_add_one h2.ne']
  ext w i
  fin_cases i <;>
    simp [matrixCLM,b,r,ContinuousLinearMap.smulRight_apply,vec2,hp1,hp2,hp3] <;>
    (rw [show z 1*2=2*z 1 by ring]; field_simp [hz.ne'] <;> ring)

lemma matrixCLM_trace (a b c d : ℝ) :
    LinearMap.trace ℝ Plane (matrixCLM a b c d).toLinearMap = a+d := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.trace_fin_two]
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr,matrixCLM_apply]

lemma matrixCLM_det (a b c d : ℝ) :
    LinearMap.det (matrixCLM a b c d).toLinearMap = a*d-b*c := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr,matrixCLM_apply]

lemma singularField_trace_det (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    LinearMap.trace ℝ Plane (fderiv ℝ (singularField p) z).toLinearMap = 0 ∧
    LinearMap.det (fderiv ℝ (singularField p) z).toLinearMap =
      ((z 1/(1/2:ℝ))^(p-2))^2*(p-1)/2*((2-p)*(z 0/z 1)^2-p) := by
  rw [singularField_fderiv p hz,matrixCLM_trace,matrixCLM_det]
  constructor <;> ring

lemma singularField_hyperbolic {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    {z : Plane} (hz : 0 < z 1) (hb : |z 0| ≤ z 1) :
    LinearMap.trace ℝ Plane (fderiv ℝ (singularField p) z).toLinearMap = 0 ∧
    LinearMap.det (fderiv ℝ (singularField p) z).toLinearMap < 0 := by
  obtain ⟨ht,hd⟩ := singularField_trace_det p hz
  refine ⟨ht,?_⟩
  rw [hd]
  have hq : |z 0/z 1| ≤ 1 := by
    rw [abs_div,abs_of_pos hz,div_le_one hz]
    exact hb
  have hq2 : (z 0/z 1)^2 ≤ 1 := by
    have := mul_self_le_mul_self (abs_nonneg (z 0/z 1)) hq
    nlinarith [sq_abs (z 0/z 1)]
  apply mul_neg_of_pos_of_neg
  · exact div_pos (mul_pos (sq_pos_of_pos (Real.rpow_pos_of_pos (by positivity) _)) (by linarith)) (by norm_num)
  · have := mul_le_mul_of_nonneg_left hq2 (sub_nonneg.mpr hp2.le)
    nlinarith

lemma singularField_scaled_hyperbolic {p c : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hc : c ≠ 0) {z : Plane} (hz : 0 < z 1) (hb : |z 0| ≤ z 1)
    (hd : |c| *‖fderiv ℝ (singularField p) z‖ < 1) :
    HyperbolicAt 1 (fun w => c • singularField p w) z := by
  have hdiff := (singularField_contDiffAt p hz).differentiableAt (by norm_num)
  rw [HyperbolicAt,fderiv_fun_const_smul hdiff]
  have htd := singularField_hyperbolic hp hp2 hz hb
  have heig := plane_hyperbolic_eigenvalues _ htd.1 htd.2
  let lam := Real.sqrt (-LinearMap.det (fderiv ℝ (singularField p) z).toLinearMap)
  have hlam : 0 < lam := Real.sqrt_pos.mpr (by linarith [htd.2])
  have hnorm : lam ≤ ‖fderiv ℝ (singularField p) z‖ := eigenvalue_le_norm _ hlam.le heig.1
  have hnonneg : 0 < |c| := abs_pos.mpr hc
  refine ⟨|c| *lam,by simpa using mul_pos hnonneg hlam,?_,?_,?_⟩
  · simpa using (mul_le_mul_of_nonneg_left hnorm hnonneg.le).trans_lt hd
  · by_cases hcp : 0 ≤ c
    · simpa [abs_of_nonneg hcp] using eigenvalue_smul _ heig.1 c
    · have hcn : c < 0 := lt_of_not_ge hcp
      simpa [abs_of_neg hcn] using eigenvalue_smul _ heig.2 c
  · by_cases hcp : 0 ≤ c
    · simpa [abs_of_nonneg hcp] using eigenvalue_smul _ heig.2 c
    · have hcn : c < 0 := lt_of_not_ge hcp
      simpa [abs_of_neg hcn] using eigenvalue_smul _ heig.1 c

end RuledApproximation

end

end OAI
