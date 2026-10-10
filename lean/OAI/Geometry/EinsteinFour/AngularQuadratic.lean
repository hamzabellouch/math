import OAI.Geometry.EinsteinFour.SphericalMoments

namespace OAI

/-! Angular averages of two quadratic forms, from the precise fourth
spherical moment. This is used for the two Weyl blocks in the normal Jacobi
matrix; no curvature average is an input. -/

namespace PositiveEinsteinFour.Angular

open MeasureTheory Matrix

noncomputable section

abbrev Mat4 := Geometry.Mat4

def quadratic (C : Mat4) (q : Directions) : ℝ :=
  ∑ i, ∑ j, C i j * (q.val i * q.val j)

theorem continuous_quadratic (C : Mat4) : Continuous (quadratic C) := by
  unfold quadratic
  fun_prop

theorem integral_quadratic_mul (h : FollandMoments) (C D : Mat4) :
    (∫ q, quadratic C q * quadratic D q ∂sphereMeasure) =
      ∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l * momentFour i j k l := by
  have hexp : (fun q => quadratic C q * quadratic D q) =
      (fun q => ∑ i, ∑ j, ∑ k, ∑ l,
        C i j * D k l * (q.val i * q.val j * q.val k * q.val l)) := by
    funext q
    unfold quadratic
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hexp, integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_const_mul, h.fourth]

/-- The finite contraction is stated on functions so that no matrix
coercion is unfolded inside the simplifier. -/
theorem fourth_sum_formula (C D : Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l * momentFour i j k l) =
      ((∑ i, C i i) * (∑ j, D j j) + (∑ i, ∑ j, C i j * D i j) +
        (∑ i, ∑ j, C i j * D j i)) / 24 := by
  have hm (i j k l : Fin 4) : C i j * D k l * momentFour i j k l =
      (C i j * D k l * delta i j * delta k l +
       C i j * D k l * delta i k * delta j l +
       C i j * D k l * delta i l * delta j k) / 24 := by
    unfold momentFour
    ring
  simp_rw [hm, ← Finset.sum_div, Finset.sum_add_distrib]
  congr 1
  simp [delta, mul_ite, Finset.sum_mul_sum]

/-- Fourth moments give the complete bilinear quadratic-form formula. -/
theorem integral_quadratic_mul_formula (h : FollandMoments) (C D : Mat4) :
    (∫ q, quadratic C q * quadratic D q ∂sphereMeasure) =
      (C.trace * D.trace + (∑ i, ∑ j, C i j * D i j) +
        (∑ i, ∑ j, C i j * D j i)) / 24 := by
  rw [integral_quadratic_mul h]
  simpa only [Matrix.trace, Matrix.diag] using! fourth_sum_formula C D

theorem integral_quadratic_mul_traceFree (h : FollandMoments) (C D : Mat4)
    (hC : C.trace = 0) (hD : D.trace = 0) (hDs : Dᵀ = D) :
    (∫ q, quadratic C q * quadratic D q ∂sphereMeasure) =
      (∑ i, ∑ j, C i j * D i j) / 12 := by
  rw [integral_quadratic_mul_formula h, hC, hD]
  have hd (i j : Fin 4) : D j i = D i j := congrFun (congrFun hDs i) j
  simp_rw [hd]
  ring

end

end PositiveEinsteinFour.Angular

end OAI
