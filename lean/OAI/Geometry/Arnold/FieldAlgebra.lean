import OAI.Geometry.Arnold.Parameter

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Field
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints ArnoldCounterexample.Factors
open scoped ContDiff Topology Matrix
open Set Filter

lemma casimir_unit (z : UnitQuadric) (hz : (z:CV) 0 = 0) : casimir z = 1 := by
  have h := (sphereFactors_mem z hz).1
  simpa [casimir, sphereFactors, sqNorm, Fin.sum_univ_succ, add_assoc] using h

lemma pairing_scale (c : ℂ) (z : CV) : pairing (c • z) = Complex.normSq c ^ 2 * pairing z := by
  simp only [pairing, left_scale, right_scale, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma casimir_scale (c : ℂ) (z : CV) : casimir (c • z) = Complex.normSq c ^ 2 * casimir z := by
  simp only [casimir, left_scale, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

lemma mixed_scale (c : ℂ) (z : CV) : mixedField (c • z) = Complex.normSq c • (c • mixedField z) := by
  simp only [mixedField, left_scale, right_scale, Pi.smul_apply, smul_eq_mul, left_phase, right_phase,
    Finset.smul_sum, smul_add, smul_comm c, smul_smul]

lemma self_scale (c : ℂ) (z : CV) : selfField (c • z) = Complex.normSq c • (c • selfField z) := by
  simp only [selfField, left_scale, Pi.smul_apply, smul_eq_mul, left_phase,
    Finset.smul_sum, smul_comm c, smul_smul]

lemma core_unit (z : UnitQuadric) (hz : (z:CV) 0 = 0) :
    core z = leftOperator 0 z - rightOperator 2 z + mixedField z - pairing z • selfField z := by
  simp only [core, casimir_unit z hz, radial_at_one.1, radial_at_one.2, one_smul]
  module

lemma core_homogeneous (z : UnitQuadric) (hz : (z:CV) 0 = 0) (c : ℂ)
    (hc : Complex.normSq c ∈ Ioo (1/2:ℝ) 2) : core (c • (z:CV)) = c • core z := by
  let r := Complex.normSq c
  have hr : r ≠ 0 := ne_of_gt (lt_trans (by norm_num) hc.1)
  have he : 2 * (-(2*r^3)⁻¹) * (r^2 * pairing z) * r = -pairing z := by
    field_simp
  rw [core, casimir_scale, casimir_unit z hz, mul_one,
    (radial_squared r hc).1, (radial_squared r hc).2, pairing_scale, mixed_scale, self_scale,
    core_unit z hz]
  simp only [left_phase, right_phase, smul_add, smul_sub, smul_smul, ← smul_comm c]
  change c • leftOperator 0 z - c • rightOperator 2 z + c • ((r⁻¹*r) • mixedField z) +
    c • ((2 * (-(2*r^3)⁻¹) * (r^2 * pairing z) * r) • selfField z) = _
  rw [inv_mul_cancel₀ hr, one_smul, he, neg_smul]
  module

lemma left_bracket (i j : Fin 3) (z : CV) : symplectic (leftOperator i z) (leftOperator j z) =
    2 * (![![0,leftSphere z 2,-leftSphere z 1], ![-leftSphere z 2,0,leftSphere z 0],
      ![leftSphere z 1,-leftSphere z 0,0]] i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [symplectic_apply, omega, leftOperator, rotor_apply, Pi.single_apply,
      leftSphere, moment_real, Fin.sum_univ_succ, Complex.mul_im] <;> ring

lemma right_bracket (i j : Fin 3) (z : CV) : symplectic (rightOperator i z) (rightOperator j z) =
    -2 * (![![0,rightSphere z 2,-rightSphere z 1], ![-rightSphere z 2,0,rightSphere z 0],
      ![rightSphere z 1,-rightSphere z 0,0]] i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [symplectic_apply, omega, rightOperator, rotor_apply, Pi.single_apply,
      rightSphere, moment_real, Fin.sum_univ_succ, Complex.mul_im] <;> ring

lemma mixed_bracket (i j : Fin 3) (z : CV) : symplectic (leftOperator i z) (rightOperator j z) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [symplectic_apply, omega, leftOperator, rightOperator, rotor_apply, Pi.single_apply,
      Fin.sum_univ_succ, Complex.mul_im] <;> ring

lemma left_core_derivative (z : UnitQuadric) (hz : (z:CV) 0 = 0) (i : Fin 3) :
    symplectic (leftOperator i z) (core z) = 2 * ((east + rightSphere z) ⨯₃ leftSphere z) i := by
  rw [core_unit z hz]
  simp only [mixedField, selfField, map_sub, map_add, map_sum, map_smul, smul_eq_mul,
    left_bracket, mixed_bracket, mul_zero, add_zero, sub_zero]
  fin_cases i <;> simp [Fin.sum_univ_succ, crossProduct, east] <;> ring

lemma right_core_derivative (z : UnitQuadric) (hz : (z:CV) 0 = 0) (i : Fin 3) :
    symplectic (rightOperator i z) (core z) = -2 * ((leftSphere z - pole) ⨯₃ rightSphere z) i := by
  have hmix (i j : Fin 3) : symplectic (rightOperator i z) (leftOperator j z) = 0 := by
    rw [symplectic_skew, mixed_bracket, neg_zero]
  rw [core_unit z hz]
  simp only [mixedField, selfField, map_sub, map_add, map_sum, map_smul, smul_eq_mul,
    right_bracket, hmix, mul_zero, zero_add]
  fin_cases i <;> simp [Fin.sum_univ_succ, crossProduct, pole] <;> ring

lemma cross_zero_multiplier (x a : R3) (hx : sqNorm x = 1) (ha : a ⨯₃ x = 0) :
    a = (a ⬝ᵥ x) • x := by
  have h := congrArg (fun y : R3 ↦ x ⨯₃ y) ha
  rw [cross_cross_eq_smul_sub_smul', map_zero] at h
  have hxx : x ⬝ᵥ x = 1 := by simpa [dotProduct, sqNorm, Fin.sum_univ_succ, pow_two, add_assoc] using hx
  rw [hxx, one_smul] at h
  exact sub_eq_zero.mp h

lemma core_vertical_critical (z : UnitQuadric) (hz : (z:CV) 0 = 0) (a : ℝ)
    (ha : core z = a • (Complex.I • (z:CV))) : MultiplierCritical (sphereFactors z) := by
  have hσ (v : CV) (hv : (bilinear (star (z:CV)) v).re = 0) :
      symplectic v (Complex.I • (z:CV)) = 0 := by
    rw [symplectic_apply]
    have he : omega v (Complex.I • (z:CV)) = 2 * (bilinear (star (z:CV)) v).re := by
      simp only [omega, bilinear, Pi.star_apply, Pi.smul_apply, smul_eq_mul,
        Complex.im_sum, Complex.re_sum, Complex.mul_im, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, hv, mul_zero]
  have hi (i : Fin 3) := hσ (leftOperator i z) (left_skew i (z:CV)).1
  have hj (i : Fin 3) := hσ (rightOperator i z) (right_skew i (z:CV)).1
  have hL : (east + rightSphere z) ⨯₃ leftSphere z = 0 := by
    ext i
    have h := left_core_derivative z hz i
    rw [ha, map_smul, hi, smul_zero] at h
    simpa only [Pi.zero_apply] using (mul_eq_zero.mp h.symm).resolve_left (by norm_num)
  have hR : (leftSphere z - pole) ⨯₃ rightSphere z = 0 := by
    ext i
    have h := right_core_derivative z hz i
    rw [ha, map_smul, hj, smul_zero] at h
    simpa only [Pi.zero_apply] using (mul_eq_zero.mp h.symm).resolve_left (by norm_num)
  have hmem := sphereFactors_mem z hz
  have eL := cross_zero_multiplier (leftSphere z) (east+rightSphere z) hmem.1 hL
  have eR := cross_zero_multiplier (rightSphere z) (leftSphere z-pole) hmem.2 hR
  refine ⟨hmem, (east+rightSphere z) ⬝ᵥ leftSphere z,
    (leftSphere z-pole) ⬝ᵥ rightSphere z, ?_⟩
  have eL0 := congrFun eL 0; have eL1 := congrFun eL 1; have eL2 := congrFun eL 2
  have eR0 := congrFun eR 0; have eR1 := congrFun eR 1; have eR2 := congrFun eR 2
  simpa [sphereFactors, east, pole] using And.intro eL0 (And.intro eL1 (And.intro eL2
    (And.intro eR0 (And.intro eR1 eR2))))

lemma core_complex_vertical_critical (z : UnitQuadric) (hz : (z:CV) 0 = 0) (c : ℂ)
    (hc : core z = c • (z:CV)) : MultiplierCritical (sphereFactors z) := by
  have hr := (core_skew (z:CV)).1
  rw [hc, bilinear_smul_right, bilinear_star_self, z.property.1] at hr
  simp only [Complex.ofReal_one, mul_one] at hr
  apply core_vertical_critical z hz c.im
  rw [hc]
  have he : c = (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hr]
  rw [he, mul_smul]
  ext i
  simp [Complex.real_smul]

end ArnoldCounterexample.Field

end

end OAI
