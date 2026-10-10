import OAI.Geometry.EinsteinFour.SphericalPairMix

namespace OAI

/-! The quartic sphere moments from the explicit orthogonal coordinate
changes. Probability normalization remains separate from the moment proof. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

variable [IsProbabilityMeasure sphereMeasure]

omit [IsProbabilityMeasure sphereMeasure] in
private theorem sqrt_two_fourth : Real.sqrt 2 ^ 4 = 4 := by
  calc
    _ = (Real.sqrt 2 ^ 2) ^ 2 := by ring
    _ = 4 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

theorem integral_fourth_three_mixed (i j : Fin 4) (hij : i ≠ j) :
    (∫ q : Directions, q.val i ^ 4 ∂sphereMeasure) =
      3 * ∫ q : Directions, q.val i ^ 2 * q.val j ^ 2 ∂sphereMeasure := by
  let f : Fin 5 → Directions → ℝ := ![
    fun q => q.val i ^ 4,
    fun q => 4 * (q.val i ^ 3 * q.val j),
    fun q => 6 * (q.val i ^ 2 * q.val j ^ 2),
    fun q => 4 * (q.val i * q.val j ^ 3),
    fun q => q.val j ^ 4]
  have hf (k : Fin 5) : Integrable (f k) sphereMeasure := by
    fin_cases k <;> dsimp [f] <;> apply sphere_continuous_integrable <;> fun_prop
  have hp (q : Directions) : (∑ k, f k q) =
      4 * ((q.val i + q.val j) / Real.sqrt 2) ^ 4 := by
    have he : q.val i ^ 4 + 4 * (q.val i ^ 3 * q.val j) +
        6 * (q.val i ^ 2 * q.val j ^ 2) + 4 * (q.val i * q.val j ^ 3) + q.val j ^ 4 =
        4 * ((q.val i + q.val j) / Real.sqrt 2) ^ 4 := by
      rw [div_pow, sqrt_two_fourth]
      ring
    simpa [f, Fin.sum_univ_succ, add_assoc] using he
  have hr := sphereIntegral_isometry (directionIsometry (pairMix i j hij))
    (fun q : Directions => q.val i ^ 4)
  have hr' : (∫ q : Directions, ((q.val i + q.val j) / Real.sqrt 2) ^ 4 ∂sphereMeasure) =
      ∫ q : Directions, q.val i ^ 4 ∂sphereMeasure := by
    change (∫ q : Directions, (pairMix i j hij q.val i) ^ 4 ∂sphereMeasure) = _ at hr
    simpa only [pairMix_coordinate, ite_true] using hr
  have hs : (∑ k, ∫ q, f k q ∂sphereMeasure) =
      4 * ∫ q : Directions, q.val i ^ 4 ∂sphereMeasure := by
    rw [← integral_finsetSum _ (fun k _ => hf k)]
    calc
      _ = ∫ q : Directions, 4 * ((q.val i + q.val j) / Real.sqrt 2) ^ 4 ∂sphereMeasure :=
        integral_congr_ae (Filter.Eventually.of_forall hp)
      _ = _ := by rw [integral_const_mul, hr']
  have hz31 := integral_two_powers_odd i j hij 3 1 (by decide)
  have hz13 := integral_two_powers_odd i j hij 1 3 (by decide)
  simp only [pow_one] at hz31 hz13
  simp [f, Fin.sum_univ_succ, integral_const_mul, hz31, hz13] at hs
  rw [integral_coordinate_pow_eq j i 4] at hs
  linarith

omit [IsProbabilityMeasure sphereMeasure] in
private theorem sum_single_exception (i : Fin 4) (a b : ℝ) :
    (∑ j : Fin 4, if j = i then a else b) = a + 3 * b := by
  have he (j : Fin 4) : (if j = i then a else b) =
      (if j = i then a - b else 0) + b := by
    split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem integral_coordinate_fourth (i : Fin 4) :
    (∫ q : Directions, q.val i ^ 4 ∂sphereMeasure) = 1 / 8 := by
  have hi (j : Fin 4) : Integrable
      (fun q : Directions => q.val i ^ 2 * q.val j ^ 2) sphereMeasure :=
    sphere_continuous_integrable (by fun_prop)
  have hs : (∑ j : Fin 4, ∫ q : Directions, q.val i ^ 2 * q.val j ^ 2 ∂sphereMeasure) =
      1 / 4 := by
    rw [← integral_finsetSum _ (fun j _ => hi j)]
    have he (q : Directions) : (∑ j, q.val i ^ 2 * q.val j ^ 2) = q.val i ^ 2 := by
      rw [← Finset.mul_sum, sum_coordinate_sq, mul_one]
    simp_rw [he]
    exact integral_coordinate_square i
  have he (j : Fin 4) :
      (∫ q : Directions, q.val i ^ 2 * q.val j ^ 2 ∂sphereMeasure) =
      if j = i then (∫ q : Directions, q.val i ^ 4 ∂sphereMeasure) else
        (∫ q : Directions, q.val i ^ 4 ∂sphereMeasure) / 3 := by
    by_cases hji : j = i
    · subst j
      simp only [ite_true, ← pow_add]
    · rw [ite_eq_right hji]
      have h := integral_fourth_three_mixed i j (Ne.symm hji)
      linarith
  simp_rw [he] at hs
  rw [sum_single_exception] at hs
  linarith

theorem integral_coordinate_square_square (i j : Fin 4) (hij : i ≠ j) :
    (∫ q : Directions, q.val i ^ 2 * q.val j ^ 2 ∂sphereMeasure) = 1 / 24 := by
  have h := integral_fourth_three_mixed i j hij
  rw [integral_coordinate_fourth] at h
  linarith

theorem actual_spherical_fourth (i j k l : Fin 4) :
    (∫ q : Directions, q.val i * q.val j * q.val k * q.val l ∂sphereMeasure) =
      momentFour i j k l := by
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      by_cases hil : i = l
      · subst l
        have he : (fun q : Directions => q.val i * q.val i * q.val i * q.val i) =
            fun q => q.val i ^ 4 := by funext q; ring
        rw [he, integral_coordinate_fourth]
        norm_num [momentFour, delta]
      · have hz : (∫ q : Directions, q.val i * q.val i * q.val i * q.val l
            ∂sphereMeasure) = 0 := by
          apply sphereIntegral_odd (coordinateFlip l)
          intro q
          simp [hil]
        rw [hz]
        simp [momentFour, delta, hil]
    · by_cases hkl : k = l
      · subst l
        have he : (fun q : Directions => q.val i * q.val i * q.val k * q.val k) =
            fun q => q.val i ^ 2 * q.val k ^ 2 := by funext q; ring
        rw [he, integral_coordinate_square_square i k hik]
        simp [momentFour, delta, hik]
      · have hz : (∫ q : Directions, q.val i * q.val i * q.val k * q.val l
            ∂sphereMeasure) = 0 := by
          apply sphereIntegral_odd (coordinateFlip k)
          intro q
          simp [hik, (Ne.symm hkl)]
        rw [hz]
        simp [momentFour, delta, hik, hkl]
  · by_cases hik : i = k
    · subst k
      by_cases hjl : j = l
      · subst l
        have he : (fun q : Directions => q.val i * q.val j * q.val i * q.val j) =
            fun q => q.val i ^ 2 * q.val j ^ 2 := by funext q; ring
        rw [he, integral_coordinate_square_square i j hij]
        simp [momentFour, delta, hij, (Ne.symm hij)]
      · have hz : (∫ q : Directions, q.val i * q.val j * q.val i * q.val l
            ∂sphereMeasure) = 0 := by
          apply sphereIntegral_odd (coordinateFlip j)
          intro q
          simp [hij, (Ne.symm hjl)]
        rw [hz]
        simp [momentFour, delta, hij, (Ne.symm hij), hjl]
    · by_cases hil : i = l
      · subst l
        by_cases hjk : j = k
        · subst k
          have he : (fun q : Directions => q.val i * q.val j * q.val j * q.val i) =
              fun q => q.val i ^ 2 * q.val j ^ 2 := by funext q; ring
          rw [he, integral_coordinate_square_square i j hij]
          simp [momentFour, delta, hij, (Ne.symm hij)]
        · have hz : (∫ q : Directions, q.val i * q.val j * q.val k * q.val i
              ∂sphereMeasure) = 0 := by
            apply sphereIntegral_odd (coordinateFlip j)
            intro q
            simp [hij, (Ne.symm hjk)]
          rw [hz]
          simp [momentFour, delta, hij, (Ne.symm hij), hik, (Ne.symm hik), hjk]
      · have hz : (∫ q : Directions, q.val i * q.val j * q.val k * q.val l
            ∂sphereMeasure) = 0 := by
          apply sphereIntegral_odd (coordinateFlip i)
          intro q
          simp [(Ne.symm hij), (Ne.symm hik), (Ne.symm hil)]
        rw [hz]
        simp [momentFour, delta, hij, hik, hil]

end
end PositiveEinsteinFour.Angular

end OAI
