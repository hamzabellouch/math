import OAI.Geometry.EinsteinFour.SphericalMeasureInvariance

namespace OAI

/-! The quadratic spherical moment follows from actual Hausdorff-measure
invariance and the unit-sphere equation. Only probability normalization is
needed; no moment identity is assumed. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

def coordinateFlip (i : Fin 4) : Directions ≃ᵢ Directions :=
  directionIsometry (LinearIsometryEquiv.piLpCongrRight 2 (fun j : Fin 4 =>
    if j = i then (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) else
      LinearIsometryEquiv.refl ℝ ℝ))

@[simp] theorem coordinateFlip_apply (i j : Fin 4) (q : Directions) :
    (coordinateFlip i q).val j = if j = i then -q.val j else q.val j := by
  classical
  by_cases h : j = i <;>
    simp [coordinateFlip, directionIsometry, LinearIsometryEquiv.piLpCongrRight_apply, h]

def coordinatePermutation (p : Equiv.Perm (Fin 4)) : Directions ≃ᵢ Directions :=
  directionIsometry (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p)

@[simp] theorem coordinatePermutation_apply (p : Equiv.Perm (Fin 4))
    (q : Directions) (j : Fin 4) :
    (coordinatePermutation p q).val j = q.val (p.symm j) := rfl

theorem sphereIntegral_odd (e : Directions ≃ᵢ Directions) (f : Directions → ℝ)
    (h : ∀ q, f (e q) = -f q) : (∫ q, f q ∂sphereMeasure) = 0 := by
  have hi := sphereIntegral_isometry e f
  have heq : (fun q => f (e q)) = fun q => -f q := funext h
  rw [heq, integral_neg] at hi
  linarith

theorem integral_coordinate_mul_zero (i j : Fin 4) (hij : i ≠ j) :
    (∫ q : Directions, q.val i * q.val j ∂sphereMeasure) = 0 := by
  apply sphereIntegral_odd (coordinateFlip i)
  intro q
  simp [hij.symm]

theorem integral_coordinate_pow_eq (i j : Fin 4) (n : ℕ) :
    (∫ q : Directions, q.val i ^ n ∂sphereMeasure) =
      ∫ q : Directions, q.val j ^ n ∂sphereMeasure := by
  have h := sphereIntegral_isometry (coordinatePermutation (Equiv.swap i j))
    (fun q : Directions => q.val i ^ n)
  simpa using h.symm

theorem integral_coordinate_square_eq (i j : Fin 4) :
    (∫ q : Directions, q.val i ^ 2 ∂sphereMeasure) =
      ∫ q : Directions, q.val j ^ 2 ∂sphereMeasure :=
  integral_coordinate_pow_eq i j 2

theorem integral_two_powers_odd (i j : Fin 4) (hij : i ≠ j) (n m : ℕ)
    (hn : Odd n) :
    (∫ q : Directions, q.val i ^ n * q.val j ^ m ∂sphereMeasure) = 0 := by
  apply sphereIntegral_odd (coordinateFlip i)
  intro q
  simp only [coordinateFlip_apply, ite_true, ite_eq_right hij.symm, hn.neg_pow, neg_mul]

theorem sum_coordinate_sq (q : Directions) : (∑ i, q.val i ^ 2) = 1 := by
  rw [← EuclideanSpace.real_norm_sq_eq, q.property]
  norm_num

def coordinateMonomial (a : Fin 4 → ℕ) (q : Directions) : ℝ :=
  ∏ i, q.val i ^ a i

theorem coordinateMonomial_flip (a : Fin 4 → ℕ) (i : Fin 4) (q : Directions) :
    coordinateMonomial a (coordinateFlip i q) =
      (-1 : ℝ) ^ a i * coordinateMonomial a q := by
  have hf (j : Fin 4) : (coordinateFlip i q).val j ^ a j =
      (if j = i then (-1 : ℝ) ^ a i else 1) * q.val j ^ a j := by
    by_cases h : j = i
    · subst j
      simp only [coordinateFlip_apply, ite_true]
      calc
        (-q.val i) ^ a i = ((-1 : ℝ) * q.val i) ^ a i := by rw [neg_one_mul]
        _ = (-1 : ℝ) ^ a i * q.val i ^ a i := mul_pow _ _ _
    · simp [h]
  unfold coordinateMonomial
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]

theorem integral_coordinateMonomial_odd (a : Fin 4 → ℕ) (i : Fin 4)
    (hi : Odd (a i)) : (∫ q, coordinateMonomial a q ∂sphereMeasure) = 0 := by
  apply sphereIntegral_odd (coordinateFlip i)
  intro q
  rw [coordinateMonomial_flip, hi.neg_one_pow, neg_one_mul]

variable [IsProbabilityMeasure sphereMeasure]

theorem sphere_continuous_integrable {f : Directions → ℝ} (hf : Continuous f) :
    Integrable f sphereMeasure :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem integral_coordinate_square (i : Fin 4) :
    (∫ q : Directions, q.val i ^ 2 ∂sphereMeasure) = 1 / 4 := by
  have hi (j : Fin 4) : Integrable (fun q : Directions => q.val j ^ 2) sphereMeasure :=
    sphere_continuous_integrable ((continuous_coordinate j).pow 2)
  have hs : (∑ j : Fin 4, ∫ q : Directions, q.val j ^ 2 ∂sphereMeasure) = 1 := by
    rw [← integral_finsetSum _ (fun j _ => hi j)]
    simp_rw [sum_coordinate_sq]
    simp
  have heq (j : Fin 4) := integral_coordinate_square_eq j i
  simp_rw [heq] at hs
  norm_num at hs
  linarith

theorem actual_spherical_second (i j : Fin 4) :
    (∫ q : Directions, q.val i * q.val j ∂sphereMeasure) = momentTwo i j := by
  by_cases hij : i = j
  · subst j
    simpa [momentTwo, delta, pow_two] using integral_coordinate_square i
  · rw [integral_coordinate_mul_zero i j hij]
    simp [momentTwo, delta, hij]

end
end PositiveEinsteinFour.Angular

end OAI
