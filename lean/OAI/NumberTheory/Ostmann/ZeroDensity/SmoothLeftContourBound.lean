import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothLeftContourWeight

namespace OAI

/-! # The uniform error from the left vertical contour -/

namespace Ostmann

open Complex MeasureTheory Filter

private theorem one_add_log_le_log_twice (q : ℝ) (hq : 1 ≤ q) :
    1 + Real.log q ≤ (1 + 1 / Real.log 2) * Real.log (2 * q) := by
  have hq0 : 0 < q := by linarith
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hlog : Real.log (2 * q) = Real.log 2 + Real.log q := Real.log_mul (by norm_num) hq0.ne'
  have hfirst : 1 ≤ Real.log (2 * q) / Real.log 2 := by
    rw [le_div_iff₀ h2]
    rw [hlog]
    linarith
  have hsecond : Real.log q ≤ Real.log (2 * q) := by rw [hlog]; linarith
  calc
    _ ≤ Real.log (2 * q) / Real.log 2 + Real.log (2 * q) := add_le_add hfirst hsecond
    _ = _ := by ring

theorem leftContourIntegrand_integrable (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 0 < X) :
    Integrable (leftContourIntegrand χ X) := by
  obtain ⟨C, hC, hbound⟩ := leftContourIntegrand_bound
  have hm := leftContourMajorant_integrable.const_mul
    (C * (1 + Real.log (χ.modulus : ℝ)) / Real.sqrt X)
  apply hm.mono' (leftContourIntegrand_continuous χ X hX).aestronglyMeasurable
  exact Eventually.of_forall (hbound χ X hX)

theorem leftContour_integral_bound : ∃ E : ℝ, 0 < E ∧
    ∀ (χ : PrimitiveComplexCharacter) (X : ℝ), 0 < X →
      ‖∫ t : ℝ, leftContourIntegrand χ X t‖ ≤
        E / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := leftContourIntegrand_bound
  let R : ℝ := |∫ t : ℝ, leftContourMajorant t| + 1
  let A : ℝ := 1 + 1 / Real.log 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hA : 0 < A := by dsimp [A]; have hh : 0 < Real.log 2 := Real.log_pos (by norm_num); positivity
  refine ⟨C * R * A, by positivity, ?_⟩
  intro χ X hX
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hlogq : 0 ≤ Real.log (χ.modulus : ℝ) := Real.log_nonneg hq
  let D := C * (1 + Real.log (χ.modulus : ℝ)) / Real.sqrt X
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hi := leftContourIntegrand_integrable χ X hX
  calc
    _ ≤ ∫ t : ℝ, ‖leftContourIntegrand χ X t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, D * leftContourMajorant t :=
      integral_mono_ae hi.norm (leftContourMajorant_integrable.const_mul D)
        (Eventually.of_forall (hbound χ X hX))
    _ = D * ∫ t : ℝ, leftContourMajorant t := integral_const_mul _ _
    _ ≤ D * R := mul_le_mul_of_nonneg_left (by dsimp [R]; linarith [le_abs_self (∫ t : ℝ, leftContourMajorant t)]) hD
    _ = (C * R / Real.sqrt X) * (1 + Real.log (χ.modulus : ℝ)) := by dsimp [D]; ring
    _ ≤ (C * R / Real.sqrt X) * (A * Real.log (2 * (χ.modulus : ℝ))) :=
      mul_le_mul_of_nonneg_left (one_add_log_le_log_twice _ hq) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
