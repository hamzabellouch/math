import OAI.Geometry.CylinderCovering.Singular.EdgeOneDifferentialDefinitions
import OAI.Geometry.CylinderCovering.Singular.EdgeOneGeometry

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SingularEdgeOne
open RuledApproximation

@[simp] lemma labelContinuous_apply (z : Plane) : labelContinuous z = labelMap z := rfl
@[simp] lemma labelContinuous_symm_apply (z : Plane) :
    labelContinuous.symm z = vec2 (2 * z 0) (z 1) := rfl

lemma edgeField_labelMap (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    edgeField p (labelMap z) = (1 / 2 : ℝ) • labelMap (singularField p z) := by
  ext i
  fin_cases i
  · change edgeU p (labelMap z 0) (labelMap z 1) =
      (1 / 2 : ℝ) * (singularField p z 0 / 2)
    rw [edgeU_labelMap]
    ring
  · change edgeV p (labelMap z 0) (labelMap z 1) =
      (1 / 2 : ℝ) * singularField p z 1
    rw [edgeV_labelMap p hz]
    ring

lemma edgeField_conjugacy (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    edgeField p z = (1 / 2 : ℝ) •
      labelContinuous (singularField p (labelContinuous.symm z)) := by
  have h := edgeField_labelMap p (z := labelContinuous.symm z) (by simpa using hz)
  simpa only [← labelContinuous_apply, ContinuousLinearEquiv.apply_symm_apply] using h

lemma edgeField_hasFDerivAt (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    HasFDerivAt (edgeField p)
      ((1 / 2 : ℝ) • labelContinuous.toContinuousLinearMap.comp
        ((fderiv ℝ (singularField p) (labelContinuous.symm z)).comp
          labelContinuous.symm.toContinuousLinearMap)) z := by
  have hz' : 0 < (labelContinuous.symm z) 1 := by simpa using hz
  have hs := (singularField_contDiffAt p hz').differentiableAt (by norm_num)
  have hd := (labelContinuous.hasFDerivAt.comp z
    (hs.hasFDerivAt.comp z labelContinuous.symm.hasFDerivAt)).const_smul (1 / 2 : ℝ)
  apply hd.congr_of_eventuallyEq
  have hpos : ∀ᶠ w : Plane in 𝓝 z, 0 < w 1 :=
    (isOpen_lt continuous_const (by fun_prop : Continuous (fun w : Plane => w 1))).mem_nhds hz
  filter_upwards [hpos] with w hw
  exact edgeField_conjugacy p hw

lemma edgeField_fderiv (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    fderiv ℝ (edgeField p) z =
      (1 / 2 : ℝ) • labelContinuous.toContinuousLinearMap.comp
        ((fderiv ℝ (singularField p) (labelContinuous.symm z)).comp
          labelContinuous.symm.toContinuousLinearMap) :=
  (edgeField_hasFDerivAt p hz).fderiv

lemma scaled_derivative_conjugacy (p c : ℝ) {z : Plane} (hz : 0 < z 1) :
    ((4 * c) / 2) • fderiv ℝ (edgeField p) (labelMap z) =
      c • labelContinuous.toContinuousLinearMap.comp
        ((fderiv ℝ (singularField p) z).comp labelContinuous.symm.toContinuousLinearMap) := by
  rw [edgeField_fderiv p (by exact hz)]
  change ((4 * c) / 2) • ((1 / 2 : ℝ) •
    labelContinuous.toContinuousLinearMap.comp
      ((fderiv ℝ (singularField p) (labelContinuous.symm (labelContinuous z))).comp
        labelContinuous.symm.toContinuousLinearMap)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, smul_smul,
    show (4 * c / 2) * (1 / 2 : ℝ) = c by ring]

lemma edgeHamiltonian_deriv_w (p w : ℝ) {l : ℝ} (hl : 0 < l) :
    deriv (fun v : ℝ => edgeHamiltonian p v l) w = edgeV p w l := by
  have hd : HasDerivAt (fun v : ℝ => edgeHamiltonian p v l)
      ((2 : ℝ) ^ (p - 3) * (2 * w * l ^ (p - 2))) w := by
    convert! (((hasDerivAt_pow 2 w).mul_const (l ^ (p - 2))).sub_const
      (l ^ p / 4)).const_mul ((2 : ℝ) ^ (p - 3)) using 1
    simp
  rw [hd.deriv, edgeV_eq p w hl, fieldQ,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hl.le]
  have ht : (2 : ℝ) ^ (p - 2) = (2 : ℝ) ^ (p - 3) * 2 := by
    rw [show p - 2 = (p - 3) + 1 by ring, Real.rpow_add_one (by norm_num)]
  rw [ht]
  ring

lemma edgeHamiltonian_deriv_l (p w : ℝ) {l : ℝ} (hl : 0 < l) :
    -deriv (fun r : ℝ => edgeHamiltonian p w r) l = edgeU p w l := by
  have hd1 := Real.hasDerivAt_rpow_const (x := l) (p := p - 2) (Or.inl hl.ne')
  have hd2 := Real.hasDerivAt_rpow_const (x := l) (p := p) (Or.inl hl.ne')
  have hd : HasDerivAt (fun r : ℝ => edgeHamiltonian p w r)
      ((2 : ℝ) ^ (p - 3) *
        (w ^ 2 * ((p - 2) * l ^ (p - 3)) - p * l ^ (p - 1) / 4)) l := by
    convert! ((hd1.const_mul (w ^ 2)).sub (hd2.div_const 4)).const_mul
      ((2 : ℝ) ^ (p - 3)) using 1
    congr 3
    ring_nf
  rw [hd.deriv, edgeU, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hl.le]
  have ht : (2 : ℝ) ^ (p - 1) = (2 : ℝ) ^ (p - 3) * 4 := by
    rw [show p - 1 = (p - 3) + 2 by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_two]
    norm_num
  have hlpow : l ^ (p - 1) = l ^ (p - 3) * l ^ 2 := by
    rw [show p - 1 = (p - 3) + 2 by ring, Real.rpow_add hl, Real.rpow_two]
  rw [ht, hlpow]
  field_simp
  ring

lemma hasEigenvalue_conjugacy (A : Plane →L[ℝ] Plane) (mu : ℝ) :
    Module.End.HasEigenvalue
      (labelContinuous.toContinuousLinearMap.comp
        (A.comp labelContinuous.symm.toContinuousLinearMap)).toLinearMap mu ↔
      Module.End.HasEigenvalue A.toLinearMap mu := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h.exists_hasEigenvector
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := labelContinuous.symm u)
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      change A (labelContinuous.symm u) = mu • labelContinuous.symm u
      have hue : labelContinuous (A (labelContinuous.symm u)) = mu • u := hu.apply_eq_smul
      have he := congrArg labelContinuous.symm hue
      simpa only [ContinuousLinearEquiv.symm_apply_apply, map_smul] using he
    · intro hu0
      apply hu.2
      have he := congrArg labelContinuous hu0
      simpa only [ContinuousLinearEquiv.apply_symm_apply, map_zero] using he
  · intro h
    obtain ⟨u, hu⟩ := h.exists_hasEigenvector
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := labelContinuous u)
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      change labelContinuous (A (labelContinuous.symm (labelContinuous u))) =
        mu • labelContinuous u
      have hue : A u = mu • u := hu.apply_eq_smul
      rw [ContinuousLinearEquiv.symm_apply_apply, hue, map_smul]
    · intro hu0
      apply hu.2
      have he := congrArg labelContinuous.symm hu0
      simpa only [ContinuousLinearEquiv.symm_apply_apply, map_zero] using he

lemma scaled_eigenvalue_iff (p c mu : ℝ) {z : Plane} (hz : 0 < z 1) :
    Module.End.HasEigenvalue
      (((4 * c) / 2) • fderiv ℝ (edgeField p) (labelMap z)).toLinearMap mu ↔
      Module.End.HasEigenvalue ((c • fderiv ℝ (singularField p) z).toLinearMap) mu := by
  rw [scaled_derivative_conjugacy p c hz]
  have he : c • labelContinuous.toContinuousLinearMap.comp
      ((fderiv ℝ (singularField p) z).comp labelContinuous.symm.toContinuousLinearMap) =
      labelContinuous.toContinuousLinearMap.comp
        ((c • fderiv ℝ (singularField p) z).comp labelContinuous.symm.toContinuousLinearMap) := by
    ext u
    simp
  rw [he]
  exact hasEigenvalue_conjugacy _ _

lemma edgeField_Hamiltonian (p w : ℝ) {l : ℝ} (hl : 0 < l) :
    edgeField p (vec2 w l) =
      vec2 (-deriv (fun r : ℝ => edgeHamiltonian p w r) l)
        (deriv (fun v : ℝ => edgeHamiltonian p v l) w) := by
  rw [edgeHamiltonian_deriv_l p w hl, edgeHamiltonian_deriv_w p w hl]
  rfl

lemma labelContinuous_matrix : labelContinuous.toContinuousLinearMap =
    matrixCLM (1 / 2) 0 0 1 := by
  ext z i
  fin_cases i <;> simp [labelContinuous, labelLinear, labelMap, matrixCLM_apply, vec2]
  ring

lemma labelContinuous_det : labelContinuous.toContinuousLinearMap.det = (1 / 2 : ℝ) := by
  rw [labelContinuous_matrix]
  change LinearMap.det (matrixCLM (1 / 2) 0 0 1).toLinearMap = _
  rw [matrixCLM_det]
  norm_num

lemma labelMap_integral_image {D : Set Plane} (hD : MeasurableSet D) (f : Plane → ℝ) :
    (∫ z in labelMap '' D, f z) = (1 / 2 : ℝ) * (∫ z in D, f (labelMap z)) := by
  change (∫ z in labelContinuous '' D, f z) = _
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hD
    (fun z _ => labelContinuous.hasFDerivAt.hasFDerivWithinAt) labelContinuous.injective.injOn]
  simp_rw [labelContinuous_det]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), smul_eq_mul]
  rw [integral_const_mul]
  rfl

lemma physicalWeight_dictionary (p c : ℝ) {z : Plane} (hz : 0 < z 1) :
    physicalWeight (1 / Real.sqrt 2) ((4 * c) • edgeField p (labelMap z)) =
      physicalWeight (Real.sqrt 2) (c • singularField p z) := by
  unfold physicalWeight
  simp only [PiLp.smul_apply, smul_eq_mul, edgeField, vec2_apply_zero, vec2_apply_one]
  rw [edgeU_labelMap, edgeV_labelMap p hz, physical_height_square,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  congr 2
  ring

lemma physical_cost_dictionary (p c : ℝ) {D : Set Plane} (hD : MeasurableSet D)
    (hpos : ∀ z ∈ D, 0 < z 1) :
    (1 / Real.sqrt 2) *
      (∫ z in labelMap '' D, physicalWeight (1 / Real.sqrt 2) ((4 * c) • edgeField p z)) =
      (Real.sqrt 2 * (∫ z in D, physicalWeight (Real.sqrt 2) (c • singularField p z))) / 4 := by
  rw [labelMap_integral_image hD]
  have hi : (∫ z in D, physicalWeight (1 / Real.sqrt 2) ((4 * c) • edgeField p (labelMap z))) =
      (∫ z in D, physicalWeight (Real.sqrt 2) (c • singularField p z)) := by
    apply setIntegral_congr_fun hD
    intro z hz
    exact physicalWeight_dictionary p c (hpos z hz)
  rw [hi, ← height_factor]
  ring

end SingularEdgeOne

end

end OAI
