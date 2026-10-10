import OAI.Analysis.BoundedHochschild.ProperlyInfiniteMatrixSystems

namespace OAI

/-!
# Isometric matrix amplification from unital isometry columns

The actual C*-matrix algebra is identified with the original algebra by
compression and reconstruction. Consequently matrix norms can be used directly
in the remaining completely bounded argument.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] {n : ℕ}
variable (c : Fin n → PartialIso M) (hi : ∀ i, (c i).initial = 1)
  (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
  (hs : ∑ i, (c i).final = 1)

include hi ho in
lemma column_star_mul (i j : Fin n) :
    star (c i : M) * (c j : M) = if i = j then 1 else 0 := by
  split_ifs with h
  · subst j
    exact hi i
  · exact PartialIso.star_mul_eq_zero_of_final_orthogonal (ho i j h)

/-- The matrix of an element with respect to unital isometry columns. -/
def columnCompression (a : M) : CStarMatrix (Fin n) (Fin n) M :=
  CStarMatrix.ofMatrix (fun i j => star (c i : M) * a * (c j : M))

/-- Reconstruction from the actual matrix entries. -/
def columnReconstruction (A : CStarMatrix (Fin n) (Fin n) M) : M :=
  ∑ i, ∑ j, (c i : M) * A i j * star (c j : M)

include hs in
lemma columnReconstruction_compression (a : M) :
    columnReconstruction c (columnCompression c a) = a := by
  calc
    _ = ∑ i, ((c i : M) * star (c i : M)) * a * (∑ j, (c j : M) * star (c j : M)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      change (c i : M) * (star (c i : M) * a * (c j : M)) * star (c j : M) = _
      simp only [mul_assoc]
    _ = a := by
      change (∑ i, (c i).final * a * (∑ j, (c j).final)) = a
      rw [hs]
      simp only [mul_one]
      rw [← Finset.sum_mul, hs, one_mul]

include hi ho in
lemma columnCompression_reconstruction (A : CStarMatrix (Fin n) (Fin n) M) :
    columnCompression c (columnReconstruction c A) = A := by
  classical
  ext i j
  change star (c i : M) * (∑ k, ∑ l, (c k : M) * A k l * star (c l : M)) * (c j : M) = A i j
  calc
    _ = ∑ k, ∑ l, (star (c i : M) * (c k : M)) * A k l *
        (star (c l : M) * (c j : M)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      simp only [mul_assoc]
    _ = A i j := by simp [column_star_mul c hi ho]

include hs in
lemma columnCompression_mul (a b : M) :
    columnCompression c (a * b) = columnCompression c a * columnCompression c b := by
  ext i j
  change star (c i : M) * (a * b) * (c j : M) =
    ∑ k, (star (c i : M) * a * (c k : M)) * (star (c k : M) * b * (c j : M))
  calc
    _ = star (c i : M) * a * (∑ k, (c k : M) * star (c k : M)) * b * (c j : M) := by
      change _ = star (c i : M) * a * (∑ k, (c k).final) * b * (c j : M)
      rw [hs, mul_one]
      simp only [mul_assoc]
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      simp only [mul_assoc]

/-- The compression/reconstruction identification preserves the C*-norm. -/
def columnMatrixEquiv : M ≃⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) M where
  toFun := columnCompression c
  invFun := columnReconstruction c
  left_inv := columnReconstruction_compression c hs
  right_inv := columnCompression_reconstruction c hi ho
  map_mul' := columnCompression_mul c hs
  map_add' a b := by
    ext i j
    change star (c i : M) * (a + b) * (c j : M) =
      star (c i : M) * a * (c j : M) + star (c i : M) * b * (c j : M)
    rw [mul_add, add_mul]
  map_smul' z a := by
    ext i j
    change star (c i : M) * (z • a) * (c j : M) = z • (star (c i : M) * a * (c j : M))
    rw [mul_smul_comm, smul_mul_assoc]
  map_star' a := by
    ext i j
    change star (c i : M) * star a * (c j : M) = star (star (c j : M) * a * (c i : M))
    simp only [star_mul, star_star, mul_assoc]

variable [PartialOrder M] [StarOrderedRing M]

include hi ho hs in
lemma columnCompression_norm (a : M) : ‖columnCompression c a‖ = ‖a‖ := by
  change ‖columnMatrixEquiv c hi ho hs a‖ = ‖a‖
  exact StarAlgEquiv.norm_map (columnMatrixEquiv c hi ho hs) a

end BoundedHochschild.KadisonRingrose

end

end OAI
