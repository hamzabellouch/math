import OAI.Geometry.EinsteinFour.AngularNormal

namespace OAI

/-! The directional-derivative part of the angular average. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

abbrev Gradient := Fin 4 → Mat3

def directional (Z : Gradient) (q : Directions) : Mat3 :=
  ∑ i, q.val i • Z i

def gradientSquareNorm (Z : Gradient) : ℝ := ∑ i, squareNorm (Z i)

private theorem integral_directional_entries (h : FollandMoments)
    (Z : Fin 4 → Fin 3 → Fin 3 → ℝ) :
    (∫ q : Directions, ∑ r, ∑ s, (∑ a, q.val a * Z a r s) ^ 2 ∂sphereMeasure) =
      (∑ a, ∑ r, ∑ s, Z a r s ^ 2) / 4 := by
  calc
    _ = ∑ r, ∫ q : Directions, ∑ s, (∑ a, q.val a * Z a r s) ^ 2 ∂sphereMeasure :=
      integral_sum h _ (fun _ => by fun_prop)
    _ = ∑ r, ∑ s, ∫ q : Directions, (∑ a, q.val a * Z a r s) ^ 2 ∂sphereMeasure := by
      apply Finset.sum_congr rfl
      intro r _
      exact integral_sum h _ (fun _ => by fun_prop)
    _ = ∑ r, ∑ s, (∑ a, Z a r s ^ 2) / 4 := by
      simp_rw [integral_directional_square h]
    _ = _ := by
      simp_rw [← Finset.sum_div]
      congr 1
      calc
        _ = ∑ r, ∑ a, ∑ s, Z a r s ^ 2 := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]

theorem integral_directional_squareNorm (h : FollandMoments) (Z : Gradient) :
    (∫ q, squareNorm (directional Z q) ∂sphereMeasure) = gradientSquareNorm Z / 4 := by
  simpa only [squareNorm, directional, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, gradientSquareNorm] using!
      integral_directional_entries h (fun a r s => Z a r s)

theorem continuous_directional (Z : Gradient) : Continuous (directional Z) := by
  unfold directional
  fun_prop

def normalDerivative (Z W : Gradient) (q : Directions) : Mat3 :=
  normalDeviation (directional Z q) (directional W q) q

/-- The two individual terms are exact directional averages; the mixed
term is retained explicitly. -/
theorem integral_normalDerivative_squareNorm (h : FollandMoments) (Z W : Gradient) :
    (∫ q, squareNorm (normalDerivative Z W q) ∂sphereMeasure) =
      (gradientSquareNorm Z + gradientSquareNorm W) / 16 +
        (∫ q, pairing (directional Z q) (rotated (directional W q) q)
          ∂sphereMeasure) / 2 := by
  have hZ : Integrable (fun q => squareNorm (directional Z q)) sphereMeasure :=
    continuous_integrable h (by
      simp only [squareNorm, directional, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      fun_prop)
  have hW : Integrable (fun q => squareNorm (directional W q)) sphereMeasure :=
    continuous_integrable h (by
      simp only [squareNorm, directional, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      fun_prop)
  have hP : Integrable
      (fun q => pairing (directional Z q) (rotated (directional W q) q)) sphereMeasure :=
    continuous_integrable h (by
      simp only [pairing, directional, rotated, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      simp only [mixingMatrix, mixing, quadratic]
      fun_prop)
  have he : (fun q => squareNorm (normalDerivative Z W q)) =
      fun q => (squareNorm (directional Z q) + squareNorm (directional W q) +
        2 * pairing (directional Z q) (rotated (directional W q) q)) / 4 := by
    funext q
    exact squareNorm_normalDeviation _ _ q
  have hZW : Integrable (fun q =>
      squareNorm (directional Z q) + squareNorm (directional W q)) sphereMeasure := hZ.add hW
  rw [he, integral_div, integral_add hZW (hP.const_mul 2),
    integral_add hZ hW, integral_const_mul,
    integral_directional_squareNorm h Z, integral_directional_squareNorm h W]
  ring

end

end PositiveEinsteinFour.Angular

end OAI
