import OAI.Geometry.RCD.Coordinates.QuadraticCoordinateGradient

namespace OAI

/-! # Gram control of the quadratic model's energy error -/

open Set MeasureTheory
open scoped NNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

private theorem quadratic_gram_error {n : ℕ} (u : Fin n → ℝ) (g : Fin n → Fin n → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hu : ∀ i, |u i| ≤ C) :
    |(∑ i, ∑ j, (u i * u j) * g j i) - ∑ i, (u i) ^ 2| ≤
      C ^ 2 * ∑ i, ∑ j, |g j i - if j = i then 1 else 0| := by
  have hdiag : (∑ i, ∑ j, (u i * u j) * (if j = i then (1 : ℝ) else 0)) =
      ∑ i, (u i) ^ 2 := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, pow_two]
  have heq : ((∑ i, ∑ j, (u i * u j) * g j i) - ∑ i, (u i) ^ 2) =
      ∑ i, ∑ j, (u i * u j) * (g j i - if j = i then 1 else 0) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hdiag]
  rw [heq]
  calc
    _ ≤ ∑ i, |∑ j, (u i * u j) * (g j i - if j = i then 1 else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |(u i * u j) * (g j i - if j = i then 1 else 0)| :=
      Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, C ^ 2 * |g j i - if j = i then 1 else 0| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      rw [abs_mul, pow_two]
      exact mul_le_mul (hu i) (hu j) (abs_nonneg _) hC
    _ = _ := by simp only [← Finset.mul_sum]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Near-orthonormal coordinate gradients make the energy density of
the actual quadratic model close to twice its value. -/
theorem coordinateQuadratic_energy_error {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (C : ℝ≥0)
    (hu : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C) :
    ∀ᵐ x ∂μ,
      |localGamma μ hQ (coordinateQuadratic μ hQ u C) (coordinateQuadratic μ hQ u C) x -
        2 * SobolevSpace.toLp μ hQ (coordinateQuadratic μ hQ u C) x| ≤
      (C : ℝ) ^ 2 * ∑ i, ∑ j, |localGamma μ hQ (u j) (u i) x - if j = i then 1 else 0| := by
  have hall := (Filter.eventually_all_finset (Finset.univ : Finset (Fin n))).mpr
    (fun j _ => hu j)
  filter_upwards [coordinateQuadratic_gradient_self μ hQ u C hu,
    coordinateQuadratic_representative μ hQ u C hu, hall] with x hg hv hb
  have hvalue : 2 * SobolevSpace.toLp μ hQ (coordinateQuadratic μ hQ u C) x =
      ∑ j, (SobolevSpace.toLp μ hQ (u j) x) ^ 2 := by
    rw [← Finset.mul_sum] at hv
    linarith
  rw [hg, hvalue]
  exact quadratic_gram_error (fun j => SobolevSpace.toLp μ hQ (u j) x)
    (fun j i => localGamma μ hQ (u j) (u i) x) C.coe_nonneg (fun j => hb j (Finset.mem_univ j))

end RegularPointCoordinates

end

end OAI
