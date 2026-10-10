import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterSiegelTools

namespace OAI

/-! # Siegel's bound for the actual primitive real zeros

The proved quadratic L-value estimate is combined with a small-power bound
for the derivative in a fixed strip. Constants may depend on the exponent.
-/

namespace Ostmann

open Complex

 theorem publishedSiegelBound : PublishedSiegelBound := by
  intro ε hε
  let η : ℝ := min (ε / 4) (1 / 4)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη4 : η ≤ 1 / 4 := min_le_right _ _
  have hηε : 3 * η ≤ ε := by have := min_le_left (ε / 4) (1 / 4); dsimp [η]; linarith
  obtain ⟨c, hc, hL⟩ := LargePrimeGaps.quadratic_siegel hη (by linarith : η ≤ 1)
  obtain ⟨K, hK, hd⟩ := character_deriv_small_power hη (by linarith : η ≤ 1 / 2)
  let D : ℝ := K * 4 ^ (2 * η)
  let C : ℝ := max (D * 3 ^ ε / c) (2 / η)
  have hD : 0 < D := mul_pos hK (Real.rpow_pos_of_pos (by norm_num) _)
  have hC : 0 < C := lt_max_of_lt_right (by positivity)
  refine ⟨C, hC, ?_⟩
  intro e
  let : NeZero e.modulus := ⟨e.positive.ne'⟩
  have hq : (1 : ℝ) ≤ e.modulus := by exact_mod_cast e.positive
  have hqpow : 1 ≤ (e.modulus : ℝ) ^ ε := Real.one_le_rpow hq hε.le
  have hgap : 0 < 1 - e.beta := sub_pos.mpr e.beta_lt_one
  by_cases hnear : 1 - η / 2 ≤ e.beta
  · let rc : PrimitiveRealCharacter := ⟨e.modulus, e.positive, e.character, e.primitive, e.nontrivial⟩
    let χ := rc.complexCharacter
    have hχ : χ ≠ 1 := rc.asComplex.nontrivial
    have hχprim : χ.IsPrimitive := rc.asComplex.primitive
    have hχquad : χ ^ 2 = 1 :=
      ((real_character_quadratic e.character).comp Complex.ofRealHom).sq_eq_one
    have hlow := hL e.modulus χ hχprim hχ hχquad
    have hzero : χ.LFunction (e.beta : ℂ) = 0 := e.zero
    have hu := character_zero_value_bound hη (by linarith) hK e.modulus χ hχ
      (hd e.modulus χ hχ) hnear e.beta_lt_one hzero
    let R : ℝ := e.modulus + 2
    have hR : 0 < R := by dsimp [R]; positivity
    have hR1 : 1 ≤ R := by dsimp [R]; linarith
    have hlowR : c * R ^ (-η) ≤ ‖χ.LFunction 1‖ := by
      apply le_trans ?_ hlow
      apply mul_le_mul_of_nonneg_left ?_ hc.le
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by dsimp [R]; linarith) (by linarith)
    have hm := mul_le_mul_of_nonneg_right (hlowR.trans hu) (Real.rpow_nonneg hR.le η)
    have he : R ^ (-η) * R ^ η = 1 := by rw [← Real.rpow_add hR]; simp
    have huR : c ≤ (1 - e.beta) * D * R ^ (3 * η) := by
      have hr : R ^ (2 * η) * R ^ η = R ^ (3 * η) := by
        rw [← Real.rpow_add hR]
        congr 1
        ring
      calc
        c = c * R ^ (-η) * R ^ η := by rw [mul_assoc c, he, mul_one]
        _ ≤ (1 - e.beta) * (D * R ^ (2 * η)) * R ^ η := hm
        _ = (1 - e.beta) * D * (R ^ (2 * η) * R ^ η) := by ring
        _ = _ := by rw [hr]
    have hpow : R ^ (3 * η) ≤ 3 ^ ε * (e.modulus : ℝ) ^ ε := by
      calc
        _ ≤ R ^ ε := Real.rpow_le_rpow_of_exponent_le hR1 hηε
        _ ≤ (3 * (e.modulus : ℝ)) ^ ε :=
          Real.rpow_le_rpow hR.le (by dsimp [R]; linarith) hε.le
        _ = _ := Real.mul_rpow (by norm_num) (by positivity)
    have hraw : c ≤ (1 - e.beta) * D * (3 ^ ε * (e.modulus : ℝ) ^ ε) :=
      huR.trans (mul_le_mul_of_nonneg_left hpow (mul_nonneg hgap.le hD.le))
    have hone : 1 ≤ (D * 3 ^ ε / c * (e.modulus : ℝ) ^ ε) * (1 - e.beta) := by
      calc
        1 = c / c := (div_self hc.ne').symm
        _ ≤ ((1 - e.beta) * D * (3 ^ ε * (e.modulus : ℝ) ^ ε)) / c :=
          div_le_div_of_nonneg_right hraw hc.le
        _ = _ := by ring
    have hbound : (1 - e.beta)⁻¹ ≤ D * 3 ^ ε / c * (e.modulus : ℝ) ^ ε := by
      rw [← one_div]
      exact (div_le_iff₀ hgap).mpr hone
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hfar : (1 - e.beta)⁻¹ ≤ 2 / η := by
      have hh := one_div_le_one_div_of_le (by positivity : 0 < η / 2)
        (show η / 2 ≤ 1 - e.beta by linarith)
      simpa only [one_div, inv_div] using hh
    exact hfar.trans ((le_max_right _ _).trans (le_mul_of_one_le_right hC.le hqpow))

end Ostmann

end OAI
