import OAI.Geometry.Arnold.MidpointDerivative

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

def kernelVector : CV := ![0,-1/4,Complex.I/4,1/4,Complex.I/4]

lemma kernelVector_ne_zero : kernelVector ≠ 0 := by
  intro h
  have := congrFun h 1
  norm_num [kernelVector] at this

lemma kernelVector_horizontal : Horizontal zeroVector kernelVector := by
  constructor <;> apply Complex.ext <;>
    norm_num [Horizontal, zeroVector, kernelVector, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im, map_ofNat, vec_five_two, vec_five_three, vec_five_four]

lemma zero_left : leftSphere zeroVector = pole := congrArg Prod.fst zeroVector_factors
lemma zero_right : rightSphere zeroVector = -east := congrArg Prod.snd zeroVector_factors
lemma zero_casimir : casimir zeroVector = 1 := casimir_unit zeroLift (by rfl)
lemma zero_pairing : pairing zeroVector = 0 := by
  simp only [pairing, zero_left, zero_right]
  norm_num [pole,east,Fin.sum_univ_succ]

lemma zero_leftOperator (i : Fin 3) : leftOperator i zeroVector =
    (![![0,Complex.I/2,1/2,-Complex.I/2,1/2],
      ![0,-1/2,Complex.I/2,1/2,Complex.I/2],
      ![0,-Complex.I/2,-1/2,-Complex.I/2,1/2]] : Fin 3 → CV) i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [leftOperator, rotor_apply, Pi.single_apply, zeroVector,
      vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, Fin.ext_iff] <;> ring

lemma zero_rightOperator (i : Fin 3) : rightOperator i zeroVector =
    (![![0,Complex.I/2,1/2,Complex.I/2,-1/2],
      ![0,-1/2,-Complex.I/2,1/2,-Complex.I/2],
      ![0,-Complex.I/2,1/2,Complex.I/2,1/2]] : Fin 3 → CV) i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [rightOperator, rotor_apply, Pi.single_apply, zeroVector,
      vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, Fin.ext_iff] <;> ring

lemma left_kernel (i : Fin 3) : symplectic (leftOperator i zeroVector) kernelVector = east i := by
  rw [zero_leftOperator, symplectic_apply]
  fin_cases i <;> norm_num [omega, kernelVector, Fin.sum_univ_succ, Complex.mul_im, east,
    vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, map_ofNat]

lemma right_kernel (i : Fin 3) : symplectic (rightOperator i zeroVector) kernelVector = 0 := by
  rw [zero_rightOperator, symplectic_apply]
  fin_cases i <;> norm_num [omega, kernelVector, Fin.sum_univ_succ, Complex.mul_im,
    vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, map_ofNat]

lemma zero_operator_cancel : rightOperator 0 zeroVector + leftOperator 2 zeroVector = 0 := by
  rw [zero_leftOperator, zero_rightOperator]
  ext i
  fin_cases i <;> norm_num [vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two] <;> ring

def kernelCurve (t : ℝ) : CV := zeroVector + t • kernelVector
lemma kernelCurve_zero : kernelCurve 0 = zeroVector := by simp [kernelCurve]
lemma kernelCurve_derivative : HasDerivAt kernelCurve kernelVector 0 := by
  convert! (hasDerivAt_const (0:ℝ) zeroVector).add ((hasDerivAt_id (0:ℝ)).smul_const kernelVector) using 1
  simp

lemma left_curve (i : Fin 3) : HasDerivAt (fun t ↦ leftSphere (kernelCurve t) i) (east i) 0 := by
  convert! (left_hasFDerivAt i (kernelCurve 0)).comp_hasDerivAt 0 kernelCurve_derivative using 1
  simp only [kernelCurve_zero, left_kernel]
lemma right_curve (i : Fin 3) : HasDerivAt (fun t ↦ rightSphere (kernelCurve t) i) 0 0 := by
  convert! (right_hasFDerivAt i (kernelCurve 0)).comp_hasDerivAt 0 kernelCurve_derivative using 1
  simp only [kernelCurve_zero, right_kernel]

lemma casimir_curve : HasDerivAt (fun t ↦ casimir (kernelCurve t)) 0 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i : Fin 3 ↦ fun _ ↦ (left_curve i).pow 2)
  convert! h using 1
  norm_num [kernelCurve_zero, zero_left, pole, east, Fin.sum_univ_succ]

lemma pairing_curve : HasDerivAt (fun t ↦ pairing (kernelCurve t)) (-1) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i : Fin 3 ↦ fun _ ↦ (left_curve i).mul (right_curve i))
  convert! h using 1
  norm_num [kernelCurve_zero, zero_left, zero_right, pole, east, Fin.sum_univ_succ]

lemma mixed_curve : HasDerivAt (fun t ↦ mixedField (kernelCurve t))
    (-leftOperator 0 kernelVector + rightOperator 2 kernelVector + rightOperator 0 zeroVector) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i : Fin 3 ↦ fun _ ↦
    ((right_curve i).smul ((leftOperator i).hasFDerivAt.comp_hasDerivAt 0 kernelCurve_derivative)).add
    ((left_curve i).smul ((rightOperator i).hasFDerivAt.comp_hasDerivAt 0 kernelCurve_derivative)))
  convert! h using 1
  simp [kernelCurve_zero, zero_left, zero_right, pole, east, Fin.sum_univ_succ]
  module

lemma core_curve : HasDerivAt (fun t ↦ core (kernelCurve t)) 0 0 := by
  have hb : HasDerivAt (fun t ↦ radial (casimir (kernelCurve t))) 0 0 := by
    convert! (radial_smooth.differentiable (by simp) (casimir (kernelCurve 0))).hasDerivAt.comp 0 casimir_curve using 1
    simp only [mul_zero]
  have hds : ContDiff ℝ ∞ (deriv radial) := (contDiff_infty_iff_deriv.mp radial_smooth).2
  have hdb : HasDerivAt (fun t ↦ deriv radial (casimir (kernelCurve t))) 0 0 := by
    convert! (hds.differentiable (by simp) (casimir (kernelCurve 0))).hasDerivAt.comp 0 casimir_curve using 1
    simp only [mul_zero]
  have hc : HasDerivAt (fun t ↦ 2 * deriv radial (casimir (kernelCurve t)) * pairing (kernelCurve t)) 1 0 := by
    convert! (hdb.const_mul 2).mul pairing_curve using 1
    simp [kernelCurve_zero, zero_casimir, zero_pairing, radial_at_one.2]
  have hs : HasDerivAt (fun t ↦ selfField (kernelCurve t))
      (fderiv ℝ selfField zeroVector kernelVector) 0 := by
    convert! (self_smooth.differentiable (by simp) (kernelCurve 0)).hasFDerivAt.comp_hasDerivAt 0 kernelCurve_derivative using 1
    simp only [kernelCurve_zero]
  have h := (((leftOperator 0).hasFDerivAt.comp_hasDerivAt 0 kernelCurve_derivative).sub
    ((rightOperator 2).hasFDerivAt.comp_hasDerivAt 0 kernelCurve_derivative)).add (hb.smul mixed_curve) |>.add (hc.smul hs)
  convert! h using 1
  simp [kernelCurve_zero, zero_casimir, zero_pairing, radial_at_one.1, selfField,
    zero_left, pole, Fin.sum_univ_succ]
  calc
    _ = rightOperator 0 zeroVector + leftOperator 2 zeroVector := zero_operator_cancel.symm
    _ = _ := by module

lemma core_kernel : fderiv ℝ core zeroVector kernelVector = 0 := by
  have h := (core_smooth.differentiable (by simp) (kernelCurve 0)).hasFDerivAt.comp_hasDerivAt 0 kernelCurve_derivative
  simpa only [kernelCurve_zero] using h.unique core_curve

lemma vectorField_zeroVector : vectorField zeroVector = 0 := by
  rw [vectorField, core_zeroVector, smul_zero]

lemma vectorField_kernel : fderiv ℝ vectorField zeroVector kernelVector = 0 := by
  have h := vectorField_local_core (by rw [zeroVector_unit.1]; norm_num : normSquared zeroVector < 4)
  rw [h.fderiv_eq]
  exact core_kernel

end ArnoldCounterexample.Construction

end

end OAI
