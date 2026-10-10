import OAI.Combinatorics.SecondNeighborhood.MatrixMaps

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable section

omit [Fintype X] [DecidableEq X] in
private theorem conflict_of_product_ne_zero
    (r : X → X → Prop) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b)
    (left right : X × X)
    (h : a left.1 right.1 * b right.2 left.2 ≠ 0) :
    Conflict r left right := by
  constructor
  · by_contra hn
    exact h (by rw [ha _ _ hn, zero_mul])
  · by_contra hn
    exact h (by rw [hb _ _ hn, mul_zero])

theorem matrixN_mul_matrixL_apply
    (r : X → X → Prop) (R C : Finset (X × X)) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b)
    (right : {right : X × X // right ∈ C})
    (left : {left : X × X // left ∈ R}) :
    (matrixN r R C b * matrixL r R C a) right left =
      a left.val.1 right.val.1 * b right.val.2 left.val.2 := by
  classical
  by_cases hprod : a left.val.1 right.val.1 * b right.val.2 left.val.2 = 0
  · rw [hprod, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hi : right.val.1 = z.val.1
    · by_cases hj : z.val.2 = left.val.2
      · rw [matrixN_apply, matrixL_apply, ite_eq_left hi, ite_eq_left hj, ← hi, hj, mul_comm]
        exact hprod
      · simp only [matrixL_apply, ite_eq_right hj, mul_zero]
    · simp only [matrixN_apply, ite_eq_right hi, zero_mul]
  · have hc : Conflict r left.val right.val :=
      conflict_of_product_ne_zero r a b ha hb left.val right.val hprod
    let z0 : {z : X × X // z ∈ Z r R C} :=
      ⟨(right.val.1, left.val.2),
        conflict_corner_mem_Z left.property right.property hc⟩
    calc
      (matrixN r R C b * matrixL r R C a) right left =
          matrixN r R C b right z0 * matrixL r R C a z0 left := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_single_of_mem z0 (Finset.mem_univ _) ?_
        intro z _ hne
        by_cases hi : right.val.1 = z.val.1
        · by_cases hj : z.val.2 = left.val.2
          · have heq : z = z0 := by
              apply Subtype.ext
              exact Prod.ext hi.symm hj
            exact (hne heq).elim
          · simp only [matrixL_apply, ite_eq_right hj, mul_zero]
        · simp only [matrixN_apply, ite_eq_right hi, zero_mul]
      _ = a left.val.1 right.val.1 * b right.val.2 left.val.2 := by
        simp [matrixN_apply, matrixL_apply, z0, mul_comm]

theorem matrixA_mul_matrixB_apply
    (r : X → X → Prop) (R C : Finset (X × X)) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b)
    (right : {right : X × X // right ∈ C})
    (left : {left : X × X // left ∈ R}) :
    (matrixA r R C a * matrixB r R C b) right left =
      a left.val.1 right.val.1 * b right.val.2 left.val.2 := by
  classical
  by_cases hprod : a left.val.1 right.val.1 * b right.val.2 left.val.2 = 0
  · rw [hprod, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro h _
    by_cases hs : right.val.2 = h.val.2
    · by_cases hp : h.val.1 = left.val.1
      · rw [matrixA_apply, matrixB_apply, ite_eq_left hs, ite_eq_left hp, ← hs, hp]
        exact hprod
      · simp only [matrixB_apply, ite_eq_right hp, mul_zero]
    · simp only [matrixA_apply, ite_eq_right hs, zero_mul]
  · have hc : Conflict r left.val right.val :=
      conflict_of_product_ne_zero r a b ha hb left.val right.val hprod
    let h0 : {h : X × X // h ∈ H r R C} :=
      ⟨(left.val.1, right.val.2),
        conflict_corner_mem_H left.property right.property hc⟩
    calc
      (matrixA r R C a * matrixB r R C b) right left =
          matrixA r R C a right h0 * matrixB r R C b h0 left := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_single_of_mem h0 (Finset.mem_univ _) ?_
        intro h _ hne
        by_cases hs : right.val.2 = h.val.2
        · by_cases hp : h.val.1 = left.val.1
          · have heq : h = h0 := by
              apply Subtype.ext
              exact Prod.ext hp hs.symm
            exact (hne heq).elim
          · simp only [matrixB_apply, ite_eq_right hp, mul_zero]
        · simp only [matrixA_apply, ite_eq_right hs, zero_mul]
      _ = a left.val.1 right.val.1 * b right.val.2 left.val.2 := by
        simp [matrixA_apply, matrixB_apply, h0]

theorem matrixN_mul_matrixL_eq_matrixA_mul_matrixB
    (r : X → X → Prop) (R C : Finset (X × X)) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b) :
    matrixN r R C b * matrixL r R C a = matrixA r R C a * matrixB r R C b := by
  ext right left
  rw [matrixN_mul_matrixL_apply r R C a b ha hb,
    matrixA_mul_matrixB_apply r R C a b ha hb]

end
end SeymourSecondNeighborhood.Pruning

end OAI
