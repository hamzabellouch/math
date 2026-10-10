import OAI.Geometry.EinsteinFour.SphericalFourthMoment

namespace OAI

/-! Actual coordinate-plane rotations on the unit sphere, with their
ordinary derivatives. These yield the sixth-moment recurrence. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour

noncomputable section

private def planeLinear (i j : Fin 4) (a b : ℝ) : FourSpace →ₗ[ℝ] FourSpace where
  toFun q := WithLp.toLp 2 (fun k => if k = i then a * q i + b * q j else
    if k = j then a * q j - b * q i else q k)
  map_add' q r := by
    ext k
    by_cases hki : k = i
    · subst k
      simp only [PiLp.add_apply, ite_true]
      ring
    · by_cases hkj : k = j
      · subst k
        simp only [PiLp.add_apply, ite_eq_right hki, ite_true]
        ring
      · simp [hki, hkj]
  map_smul' c q := by
    ext k
    by_cases hki : k = i
    · subst k
      simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, ite_true]
      ring
    · by_cases hkj : k = j
      · subst k
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
          ite_eq_right hki, ite_true]
        ring
      · simp [hki, hkj]

private theorem planeLinear_apply (i j k : Fin 4) (a b : ℝ) (q : FourSpace) :
    planeLinear i j a b q k = if k = i then a * q i + b * q j else
      if k = j then a * q j - b * q i else q k := rfl

private theorem planeLinear_norm (i j : Fin 4) (hij : i ≠ j)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (q : FourSpace) :
    ‖planeLinear i j a b q‖ = ‖q‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have hd (k : Fin 4) : (planeLinear i j a b q k) ^ 2 - q k ^ 2 =
      (if k = i then (a * q i + b * q j) ^ 2 - q i ^ 2 else 0) +
      (if k = j then (a * q j - b * q i) ^ 2 - q j ^ 2 else 0) := by
    by_cases hki : k = i
    · subst k
      simp [planeLinear_apply, hij]
    · by_cases hkj : k = j
      · subst k
        simp [planeLinear_apply, hij.symm]
      · simp [planeLinear_apply, hki, hkj]
  have hs : (∑ k : Fin 4, ((planeLinear i j a b q k) ^ 2 - q k ^ 2)) = 0 := by
    simp_rw [hd]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    calc
      _ = (a ^ 2 + b ^ 2 - 1) * (q i ^ 2 + q j ^ 2) := by ring
      _ = 0 := by rw [hab]; ring
  rw [Finset.sum_sub_distrib] at hs
  linarith

private theorem planeLinear_inverse (i j : Fin 4) (hij : i ≠ j)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    Function.LeftInverse (planeLinear i j a (-b)) (planeLinear i j a b) := by
  intro q
  ext k
  by_cases hki : k = i
  · subst k
    simp only [planeLinear_apply, ite_true, ite_eq_right hij.symm]
    calc
      _ = (a ^ 2 + b ^ 2) * q i := by ring
      _ = _ := by rw [hab]; ring
  · by_cases hkj : k = j
    · subst k
      simp only [planeLinear_apply, ite_true, ite_eq_right hij.symm]
      calc
        _ = (a ^ 2 + b ^ 2) * q j := by ring
        _ = _ := by rw [hab]; ring
    · simp [planeLinear_apply, hki, hkj]

private def planeIsometry (i j : Fin 4) (hij : i ≠ j)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) : FourSpace ≃ₗᵢ[ℝ] FourSpace where
  toLinearEquiv :=
    { planeLinear i j a b with
      invFun := planeLinear i j a (-b)
      left_inv := planeLinear_inverse i j hij a b hab
      right_inv := by
        intro q
        change planeLinear i j a b (planeLinear i j a (-b) q) = q
        have h := planeLinear_inverse i j hij a (-b) (by simpa using hab)
        simpa only [neg_neg] using h q }
  norm_map' := planeLinear_norm i j hij a b hab

def planeRotation (i j : Fin 4) (hij : i ≠ j) (t : ℝ) :
    FourSpace ≃ₗᵢ[ℝ] FourSpace :=
  planeIsometry i j hij (Real.cos t) (Real.sin t) (by
    nlinarith [Real.sin_sq_add_cos_sq t])

@[simp] theorem planeRotation_apply (i j : Fin 4) (hij : i ≠ j)
    (t : ℝ) (q : FourSpace) (k : Fin 4) :
    planeRotation i j hij t q k =
      if k = i then Real.cos t * q i + Real.sin t * q j else
      if k = j then Real.cos t * q j - Real.sin t * q i else q k := rfl

theorem planeRotation_zero (i j : Fin 4) (hij : i ≠ j) (q : FourSpace) :
    planeRotation i j hij 0 q = q := by
  ext k
  simp only [planeRotation_apply, Real.cos_zero, Real.sin_zero, one_mul, zero_mul,
    add_zero, sub_zero]
  split_ifs <;> simp_all

def planeCoordinateDerivative (i j : Fin 4) (t : ℝ) (q : FourSpace) (k : Fin 4) : ℝ :=
  if k = i then -Real.sin t * q i + Real.cos t * q j else
    if k = j then -Real.sin t * q j - Real.cos t * q i else 0

theorem hasDerivAt_planeRotation_coordinate (i j : Fin 4) (hij : i ≠ j)
    (q : FourSpace) (k : Fin 4) (t : ℝ) :
    HasDerivAt (fun s => planeRotation i j hij s q k)
      (planeCoordinateDerivative i j t q k) t := by
  simp only [planeRotation_apply, planeCoordinateDerivative]
  by_cases hki : k = i
  · simp only [ite_eq_left hki]
    exact ((Real.hasDerivAt_cos t).mul_const (q i)).add
      ((Real.hasDerivAt_sin t).mul_const (q j))
  · by_cases hkj : k = j
    · simp only [ite_eq_right hki, ite_eq_left hkj]
      exact ((Real.hasDerivAt_cos t).mul_const (q j)).sub
        ((Real.hasDerivAt_sin t).mul_const (q i))
    · simp only [ite_eq_right hki, ite_eq_right hkj]
      exact hasDerivAt_const t (q k)

theorem continuous_planeRotation_coordinate (i j : Fin 4) (hij : i ≠ j) (k : Fin 4) :
    Continuous (fun p : ℝ × Directions => planeRotation i j hij p.1 p.2.val k) := by
  simp only [planeRotation_apply]
  by_cases hki : k = i
  · simp only [ite_eq_left hki]
    fun_prop
  · by_cases hkj : k = j
    · simp only [ite_eq_right hki, ite_eq_left hkj]
      fun_prop
    · simp only [ite_eq_right hki, ite_eq_right hkj]
      fun_prop

theorem continuous_planeCoordinateDerivative (i j k : Fin 4) :
    Continuous (fun p : ℝ × Directions => planeCoordinateDerivative i j p.1 p.2.val k) := by
  unfold planeCoordinateDerivative
  by_cases hki : k = i
  · simp only [ite_eq_left hki]
    fun_prop
  · by_cases hkj : k = j
    · simp only [ite_eq_right hki, ite_eq_left hkj]
      fun_prop
    · simp only [ite_eq_right hki, ite_eq_right hkj]
      fun_prop

theorem planeCoordinateDerivative_zero (i j : Fin 4) (hij : i ≠ j)
    (q : FourSpace) (k : Fin 4) :
    planeCoordinateDerivative i j 0 q k = delta k i * q j - delta k j * q i := by
  unfold planeCoordinateDerivative delta
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [hij.symm]
    · simp [hki, hkj]

end
end PositiveEinsteinFour.Angular

end OAI
