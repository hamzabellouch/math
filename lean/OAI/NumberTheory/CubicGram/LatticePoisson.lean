import Mathlib
import OAI.NumberTheory.CubicGram.EuclideanDomain
import OAI.NumberTheory.CubicGram.Periodization

namespace OAI

/-! Eisenstein real coordinates, measure factors and translated lattice Poisson summation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology

namespace CubicFirstMoment
open CubicPoisson

def complexOfRealCoords : (Fin 2 → ℝ) →ₗ[ℝ] ℂ where
  toFun x := (x 0 : ℂ) + (x 1 : ℂ) * omega
  map_add' x y := by simp only [Pi.add_apply, Complex.ofReal_add]; ring
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
      Complex.real_smul]
    ring

lemma complexOfRealCoords_injective : Function.Injective complexOfRealCoords := by
  intro x y h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  change ((x 0 : ℂ) + (x 1 : ℂ) * omega).im =
    ((y 0 : ℂ) + (y 1 : ℂ) * omega).im at him
  change ((x 0 : ℂ) + (x 1 : ℂ) * omega).re =
    ((y 0 : ℂ) + (y 1 : ℂ) * omega).re at hre
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    omega_im, omega_re, zero_mul, zero_add, add_zero] at him
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
    omega_im, omega_re, zero_mul, sub_zero] at hre
  have hs : 0 < Real.sqrt (3 : ℝ) := by positivity
  have he : x 1 = y 1 := (mul_right_cancel₀ (by positivity : Real.sqrt (3 : ℝ) / 2 ≠ 0)) him
  ext i
  fin_cases i
  · change x 0 = y 0
    linarith
  · exact he

lemma complexOfRealCoords_surjective : Function.Surjective complexOfRealCoords := by
  intro z
  refine ⟨![z.re + z.im / Real.sqrt 3, 2 * z.im / Real.sqrt 3], ?_⟩
  exact (complex_coordinates z).symm

def eisensteinRealCoords : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  (LinearEquiv.ofBijective complexOfRealCoords
    ⟨complexOfRealCoords_injective, complexOfRealCoords_surjective⟩).toContinuousLinearEquiv

@[simp] lemma eisensteinRealCoords_apply (x : Fin 2 → ℝ) :
    eisensteinRealCoords x = (x 0 : ℂ) + (x 1 : ℂ) * omega := rfl

lemma eisensteinRealCoords_integer (n : Fin 2 → ℤ) :
    eisensteinRealCoords (fun i => (n i : ℝ)) = (ofCoords (n 0) (n 1) : ℂ) := by
  simp [ofCoords_coe]

private def realCoordMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, -1/2; 0, Real.sqrt 3 / 2]

private lemma realCoordMatrix_det : realCoordMatrix.det = Real.sqrt 3 / 2 := by
  simp [realCoordMatrix, Matrix.det_fin_two]

private lemma realCoordMatrix_apply (x : Fin 2 → ℝ) :
    Matrix.toLin' realCoordMatrix x = Complex.measurableEquivPi (eisensteinRealCoords x) := by
  ext i
  fin_cases i <;>
    simp [realCoordMatrix, Matrix.toLin'_apply, Matrix.mulVec,
      omega_re, omega_im, Matrix.vecHead, Matrix.vecTail, mul_comm]

lemma eisensteinRealCoords_map_volume :
    Measure.map eisensteinRealCoords volume =
      ENNReal.ofReal (2 / Real.sqrt 3) • (volume : Measure ℂ) := by
  have hs : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (M := realCoordMatrix) (by rw [realCoordMatrix_det]; positivity)
  have he : (eisensteinRealCoords : (Fin 2 → ℝ) → ℂ) =
      Complex.measurableEquivPi.symm ∘ Matrix.toLin' realCoordMatrix := by
    funext x
    simp only [Function.comp_apply, realCoordMatrix_apply, MeasurableEquiv.symm_apply_apply]
  rw [he, ← Measure.map_map Complex.measurableEquivPi.symm.measurable
    (Matrix.toLin' realCoordMatrix).continuous_of_finiteDimensional.measurable, hm,
    Measure.map_smul _ Complex.measurableEquivPi.symm.measurable.aemeasurable,
    Complex.volume_preserving_equiv_pi.symm.map_eq, realCoordMatrix_det]
  congr 1
  rw [abs_of_pos (inv_pos.mpr (by positivity : 0 < Real.sqrt (3 : ℝ) / 2))]
  field_simp

lemma integral_eisensteinRealCoords (f : ℂ → ℂ) :
    ∫ x : Fin 2 → ℝ, f (eisensteinRealCoords x) =
      (2 / Real.sqrt 3 : ℝ) • ∫ z : ℂ, f z := by
  have h := integral_map_equiv (μ := volume) eisensteinRealCoords.toHomeomorph.toMeasurableEquiv f
  rw [show ((eisensteinRealCoords.toHomeomorph.toMeasurableEquiv : (Fin 2 → ℝ) → ℂ)) =
    eisensteinRealCoords from rfl, eisensteinRealCoords_map_volume, integral_smul_measure] at h
  simpa only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 / Real.sqrt 3)] using h.symm

def traceLambda : ℂ := 1 + 2 * omega

lemma traceLambda_eq : traceLambda = (Real.sqrt 3 : ℂ) * Complex.I := by
  rw [traceLambda, omega_eq]
  push_cast
  ring

lemma traceLambda_ne_zero : traceLambda ≠ 0 := by
  rw [traceLambda_eq]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) Complex.I_ne_zero

def tracePair (z w : ℂ) : ℝ := 2 * (z * w).re

def traceFourier (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∫ z : ℂ, (Real.fourierChar (-tracePair z w) : ℂ) * f z

def dualRealCoords (y : Fin 2 → ℝ) : ℂ :=
  ((y 0 / 2 : ℝ) : ℂ) - (((y 0 + 2 * y 1) / (2 * Real.sqrt 3) : ℝ) : ℂ) * Complex.I

lemma dualRealCoords_trace (x y : Fin 2 → ℝ) :
    tracePair (eisensteinRealCoords x) (dualRealCoords y) = ∑ i, x i * y i := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  simp only [tracePair, eisensteinRealCoords_apply, dualRealCoords,
    Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.sub_im, Complex.mul_im, omega_re, omega_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, zero_add, add_zero,
    zero_sub, sub_zero, mul_one, Fin.sum_univ_two]
  field_simp
  ring

lemma dualRealCoords_eq (y : Fin 2 → ℝ) :
    dualRealCoords y =
      ((y 0 + y 1 : ℝ) + (y 0 : ℂ) * omega) / traceLambda := by
  apply (eq_div_iff traceLambda_ne_zero).mpr
  rw [traceLambda_eq, omega_eq]
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  simp only [dualRealCoords]
  push_cast
  field_simp
  linear_combination -(y 0 + 2 * y 1 : ℂ) * (Complex.I_sq)

def dualIntegerEquiv : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun n := ![n 0 + n 1, n 0]
  invFun m := ![m 1, m 0 - m 1]
  left_inv n := by ext i; fin_cases i <;> simp
  right_inv m := by ext i; fin_cases i <;> simp

def eisensteinPullback (f : 𝓢(ℂ, ℂ)) : 𝓢(Fin 2 → ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eisensteinRealCoords f

lemma coordinateFourier_eisenstein (f : 𝓢(ℂ, ℂ)) (y : Fin 2 → ℝ) :
    coordinateFourier (eisensteinPullback f) y =
      (2 / Real.sqrt 3 : ℝ) • traceFourier f (dualRealCoords y) := by
  rw [coordinateFourier_apply, traceFourier]
  convert integral_eisensteinRealCoords
    (fun z => (Real.fourierChar (-tracePair z (dualRealCoords y)) : ℂ) * f z) using 1
  apply integral_congr_ae
  filter_upwards with x
  simp only [dualRealCoords_trace, eisensteinPullback,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]

lemma coordinatesEquiv_coe (n : Fin 2 → ℤ) :
    (coordinatesEquiv n : ℂ) = eisensteinRealCoords (fun i => (n i : ℝ)) := by
  simp [coordinatesEquiv, coordinatesMap, ofCoords_coe]

lemma dualRealCoords_integer (n : Fin 2 → ℤ) :
    dualRealCoords (fun i => (n i : ℝ)) =
      (coordinatesEquiv (dualIntegerEquiv n) : ℂ) / traceLambda := by
  rw [dualRealCoords_eq, coordinatesEquiv_coe]
  simp [dualIntegerEquiv]

theorem poisson_eisenstein (f : 𝓢(ℂ, ℂ)) :
    ∑' a : Eisenstein, f (a : ℂ) =
      (2 / Real.sqrt 3 : ℝ) •
        ∑' h : Eisenstein, traceFourier f ((h : ℂ) / traceLambda) := by
  calc
    _ = ∑' n : Fin 2 → ℤ, eisensteinPullback f (fun i => (n i : ℝ)) := by
      have he := coordinatesEquiv.toEquiv.tsum_eq (fun a : Eisenstein => f (a : ℂ))
      change (∑' n : Fin 2 → ℤ, f (coordinatesEquiv n : ℂ)) = _ at he
      simpa only [coordinatesEquiv_coe, eisensteinPullback,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply] using he.symm
    _ = ∑' n : Fin 2 → ℤ,
        coordinateFourier (eisensteinPullback f) (fun i => (n i : ℝ)) :=
      poisson_coordinates_zero _
    _ = ∑' n : Fin 2 → ℤ,
        (2 / Real.sqrt 3 : ℝ) • traceFourier f
          ((coordinatesEquiv (dualIntegerEquiv n) : ℂ) / traceLambda) := by
      congr 1
      funext n
      rw [coordinateFourier_eisenstein, dualRealCoords_integer]
    _ = ∑' h : Eisenstein, (2 / Real.sqrt 3 : ℝ) •
        traceFourier f ((h : ℂ) / traceLambda) :=
      (dualIntegerEquiv.trans coordinatesEquiv.toEquiv).tsum_eq
        (fun h : Eisenstein => (2 / Real.sqrt 3 : ℝ) •
          traceFourier f ((h : ℂ) / traceLambda))
    _ = _ := tsum_const_smul'' _

lemma tracePair_add_left (z x w : ℂ) :
    tracePair (z + x) w = tracePair z w + tracePair x w := by
  simp only [tracePair, add_mul, Complex.add_re]
  ring

lemma traceFourier_translation (f : ℂ → ℂ) (z w : ℂ) :
    traceFourier (fun x => f (z + x)) w =
      (Real.fourierChar (tracePair z w) : ℂ) * traceFourier f w := by
  have he (x : ℂ) : (Real.fourierChar (-tracePair x w) : ℂ) * f (z + x) =
      (Real.fourierChar (tracePair z w) : ℂ) *
        ((Real.fourierChar (-tracePair (z + x) w) : ℂ) * f (z + x)) := by
    rw [show -tracePair x w = tracePair z w + -tracePair (z + x) w by
      rw [tracePair_add_left]; ring, AddChar.map_add_eq_mul, Circle.coe_mul]
    rw [mul_assoc]
  simp only [traceFourier, he, integral_const_mul]
  rw [integral_add_left_eq_self (fun x : ℂ =>
    (Real.fourierChar (-tracePair x w) : ℂ) * f x) z]

theorem poisson_eisenstein_translate (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    ∑' a : Eisenstein, f (z + (a : ℂ)) =
      (2 / Real.sqrt 3 : ℝ) • ∑' h : Eisenstein,
        (Real.fourierChar (tracePair z ((h : ℂ) / traceLambda)) : ℂ) *
          traceFourier f ((h : ℂ) / traceLambda) := by
  have he := poisson_eisenstein (f.compSubConstCLM ℂ (-z))
  have hfun : (⇑(f.compSubConstCLM ℂ (-z))) = (fun x => f (z + x)) := by
    funext x
    simp [add_comm]
  simpa only [hfun, traceFourier_translation] using he

def complexMulEquiv (q : ℂ) (hq : q ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  ((LinearEquiv.smulOfNeZero ℂ ℂ q hq).restrictScalars ℝ).toContinuousLinearEquiv

@[simp] lemma complexMulEquiv_apply (q : ℂ) (hq : q ≠ 0) (z : ℂ) :
    complexMulEquiv q hq z = q * z := rfl

private def complexMulMatrix (q : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![q.re, -q.im; q.im, q.re]

private lemma complexMulMatrix_det (q : ℂ) :
    (complexMulMatrix q).det = Complex.normSq q := by
  simp [complexMulMatrix, Matrix.det_fin_two, Complex.normSq_apply]

private lemma complexMulMatrix_apply (q : ℂ) (x : Fin 2 → ℝ) :
    Complex.measurableEquivPi.symm (Matrix.toLin' (complexMulMatrix q) x) =
      q * Complex.measurableEquivPi.symm x := by
  apply Complex.ext <;>
    simp [complexMulMatrix, Matrix.toLin'_apply,
      Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im]
  <;> ring

lemma complexMul_map_volume (q : ℂ) (hq : q ≠ 0) :
    Measure.map (fun z : ℂ => q * z) volume =
      ENNReal.ofReal (Complex.normSq q)⁻¹ • (volume : Measure ℂ) := by
  have hn : 0 < Complex.normSq q := Complex.normSq_pos.mpr hq
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (M := complexMulMatrix q) (by rw [complexMulMatrix_det]; positivity)
  have he : (fun z : ℂ => q * z) ∘ Complex.measurableEquivPi.symm =
      Complex.measurableEquivPi.symm ∘ Matrix.toLin' (complexMulMatrix q) := by
    funext x
    exact (complexMulMatrix_apply q x).symm
  calc
    _ = Measure.map (fun z : ℂ => q * z)
        (Measure.map Complex.measurableEquivPi.symm volume) := by
      rw [Complex.volume_preserving_equiv_pi.symm.map_eq]
    _ = Measure.map Complex.measurableEquivPi.symm
        (Measure.map (Matrix.toLin' (complexMulMatrix q)) volume) := by
      rw [Measure.map_map (by fun_prop) Complex.measurableEquivPi.symm.measurable, he,
        Measure.map_map Complex.measurableEquivPi.symm.measurable
          (Matrix.toLin' (complexMulMatrix q)).continuous_of_finiteDimensional.measurable]
    _ = _ := by
      rw [hm, Measure.map_smul _ Complex.measurableEquivPi.symm.measurable.aemeasurable,
        Complex.volume_preserving_equiv_pi.symm.map_eq,
        complexMulMatrix_det, abs_of_pos (inv_pos.mpr hn), ENNReal.ofReal_inv_of_pos hn]

lemma integral_complexMul (q : ℂ) (hq : q ≠ 0) (f : ℂ → ℂ) :
    ∫ z : ℂ, f (q * z) = (Complex.normSq q)⁻¹ • ∫ z : ℂ, f z := by
  have h := integral_map_equiv (μ := volume)
    (complexMulEquiv q hq).toHomeomorph.toMeasurableEquiv f
  change (∫ z : ℂ, f z ∂Measure.map (fun z => q * z) volume) =
    ∫ z : ℂ, f (q * z) at h
  rw [complexMul_map_volume q hq, integral_smul_measure] at h
  simpa only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (Complex.normSq_nonneg q),
    ENNReal.toReal_ofReal (inv_nonneg.mpr (Complex.normSq_nonneg q))] using h.symm

lemma traceFourier_complexMul (q : ℂ) (hq : q ≠ 0) (f : ℂ → ℂ) (w : ℂ) :
    traceFourier (fun z => f (q * z)) w =
      (Complex.normSq q)⁻¹ • traceFourier f (w / q) := by
  unfold traceFourier
  convert integral_complexMul q hq
    (fun z => (Real.fourierChar (-tracePair z (w / q)) : ℂ) * f z) using 1
  apply integral_congr_ae
  filter_upwards with z
  congr 2
  unfold tracePair
  congr 2
  field_simp

theorem poisson_eisenstein_coset (f : 𝓢(ℂ, ℂ)) (q : ℂ) (hq : q ≠ 0) (z : ℂ) :
    ∑' a : Eisenstein, f (z + q * (a : ℂ)) =
      (2 / (Real.sqrt 3 * Complex.normSq q) : ℝ) • ∑' h : Eisenstein,
        (Real.fourierChar (tracePair z ((h : ℂ) / (q * traceLambda))) : ℂ) *
          traceFourier f ((h : ℂ) / (q * traceLambda)) := by
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (complexMulEquiv q hq) f
  have hg : (g : ℂ → ℂ) = (fun x => f (q * x)) := rfl
  have he := poisson_eisenstein_translate g (z / q)
  rw [hg] at he
  simp_rw [mul_add, mul_div_cancel₀ z hq, traceFourier_complexMul q hq] at he
  have hfreq (h : Eisenstein) : ((h : ℂ) / traceLambda) / q =
      (h : ℂ) / (q * traceLambda) := by ring
  have hphase (h : Eisenstein) : tracePair (z / q) ((h : ℂ) / traceLambda) =
      tracePair z ((h : ℂ) / (q * traceLambda)) := by
    unfold tracePair
    congr 2
    ring
  simp_rw [hfreq, hphase, mul_smul_comm] at he
  rw [tsum_const_smul'', smul_smul] at he
  convert he using 1
  congr 1
  ring

end CubicFirstMoment

end
end

end OAI
