import OAI.Geometry.EinsteinFour.SphericalSecondMoment

namespace OAI

/-! A forty-five degree orthogonal change in a coordinate plane. This fixed
finite-dimensional change gives the fourth and sixth sphere moments. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour

noncomputable section

private def pairMixLinear (i j : Fin 4) : FourSpace →ₗ[ℝ] FourSpace where
  toFun q := WithLp.toLp 2 (fun k => if k = i then (q i + q j) / Real.sqrt 2 else
    if k = j then (q i - q j) / Real.sqrt 2 else q k)
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
  map_smul' a q := by
    ext k
    by_cases hki : k = i
    · subst k
      simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, ite_true]
      ring
    · by_cases hkj : k = j
      · subst k
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, ite_eq_right hki, ite_true]
        ring
      · simp [hki, hkj]

private theorem pairMix_apply (i j k : Fin 4) (q : FourSpace) :
    pairMixLinear i j q k = if k = i then (q i + q j) / Real.sqrt 2 else
      if k = j then (q i - q j) / Real.sqrt 2 else q k := rfl

private theorem pairMix_norm (i j : Fin 4) (hij : i ≠ j) (q : FourSpace) :
    ‖pairMixLinear i j q‖ = ‖q‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have hd (k : Fin 4) : (pairMixLinear i j q k) ^ 2 - q k ^ 2 =
      (if k = i then ((q i + q j) / Real.sqrt 2) ^ 2 - q i ^ 2 else 0) +
      (if k = j then ((q i - q j) / Real.sqrt 2) ^ 2 - q j ^ 2 else 0) := by
    by_cases hki : k = i
    · subst k
      simp [pairMix_apply, hij]
    · by_cases hkj : k = j
      · subst k
        simp [pairMix_apply, hij.symm]
      · simp [pairMix_apply, hki, hkj]
  have hs : (∑ k : Fin 4, ((pairMixLinear i j q k) ^ 2 - q k ^ 2)) = 0 := by
    simp_rw [hd]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [Finset.sum_sub_distrib] at hs
  linarith

private theorem pairMix_involutive (i j : Fin 4) (hij : i ≠ j) :
    Function.Involutive (pairMixLinear i j) := by
  intro q
  ext k
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  by_cases hki : k = i
  · subst k
    simp only [pairMix_apply, ite_true, ite_eq_right hij.symm]
    calc
      _ = (2 * q i) / (Real.sqrt 2 ^ 2) := by ring
      _ = _ := by rw [hs]; ring
  · by_cases hkj : k = j
    · subst k
      simp only [pairMix_apply, ite_eq_right hij.symm, ite_eq_left]
      calc
        _ = (2 * q j) / (Real.sqrt 2 ^ 2) := by ring
        _ = _ := by rw [hs]; ring
    · simp [pairMix_apply, hki, hkj]

def pairMix (i j : Fin 4) (hij : i ≠ j) : FourSpace ≃ₗᵢ[ℝ] FourSpace where
  toLinearEquiv :=
    { pairMixLinear i j with
      invFun := pairMixLinear i j
      left_inv := pairMix_involutive i j hij
      right_inv := pairMix_involutive i j hij }
  norm_map' := pairMix_norm i j hij

@[simp] theorem pairMix_coordinate (i j : Fin 4) (hij : i ≠ j)
    (q : FourSpace) (k : Fin 4) :
    pairMix i j hij q k = if k = i then (q i + q j) / Real.sqrt 2 else
      if k = j then (q i - q j) / Real.sqrt 2 else q k := rfl

end
end PositiveEinsteinFour.Angular

end OAI
