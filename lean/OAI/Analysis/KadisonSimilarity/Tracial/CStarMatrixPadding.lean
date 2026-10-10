import OAI.Analysis.KadisonSimilarity.Representation.SquareArrayPadding
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialSymmetryExtraction

namespace OAI

/-!
# Isometric zero padding of C-star matrices

Padding along an injection is a nonunital star algebra monomorphism. Its
isometry follows from the C-star norm theorem, and its represented action is
the concrete zero extension on finite Hilbert sums.
-/

noncomputable section
namespace KadisonSimilarity

section AlgebraicPadding

variable {A : Type*} [CStarAlgebra A] {r m : ℕ}

/-- A square matrix with zero entries outside the embedded index set. -/
def matrixZeroPadding (e : Fin r ↪ Fin m) (X : Matrix (Fin r) (Fin r) A) :
    Matrix (Fin m) (Fin m) A :=
  fun i j => ∑ p : Fin r, ∑ q : Fin r,
    if i = e p ∧ j = e q then X p q else 0

@[simp] theorem matrixZeroPadding_apply_image (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) A) (i j : Fin r) :
    matrixZeroPadding e X (e i) (e j) = X i j := by
  simp [matrixZeroPadding, e.injective.eq_iff, ite_and]

theorem matrixZeroPadding_not_mem_left (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) A) (i j : Fin m) (hi : i ∉ Set.range e) :
    matrixZeroPadding e X i j = 0 := by
  have h (p : Fin r) : i ≠ e p := fun hp => hi ⟨p, hp.symm⟩
  simp [matrixZeroPadding, h]

theorem matrixZeroPadding_not_mem_right (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) A) (i j : Fin m) (hj : j ∉ Set.range e) :
    matrixZeroPadding e X i j = 0 := by
  have h (q : Fin r) : j ≠ e q := fun hq => hj ⟨q, hq.symm⟩
  simp [matrixZeroPadding, h]

private theorem matrixPadding_sum {M : Type*} [AddCommMonoid M]
    (e : Fin r ↪ Fin m) (f : Fin m → M)
    (hf : ∀ j, j ∉ Set.range e → f j = 0) :
    ∑ j : Fin m, f j = ∑ i : Fin r, f (e i) := by
  calc
    _ = ∑ j ∈ Finset.univ.map e, f j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      apply hf
      rintro ⟨i, rfl⟩
      exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    _ = _ := by rw [Finset.sum_map]

theorem matrixZeroPadding_mul (e : Fin r ↪ Fin m)
    (X Y : Matrix (Fin r) (Fin r) A) :
    matrixZeroPadding e (X * Y) = matrixZeroPadding e X * matrixZeroPadding e Y := by
  ext i j
  by_cases hi : i ∈ Set.range e
  · obtain ⟨p, rfl⟩ := hi
    by_cases hj : j ∈ Set.range e
    · obtain ⟨q, rfl⟩ := hj
      rw [matrixZeroPadding_apply_image, Matrix.mul_apply, Matrix.mul_apply]
      rw [matrixPadding_sum e _ (by
        intro k hk
        rw [matrixZeroPadding_not_mem_right e X (e p) k hk, zero_mul])]
      simp only [matrixZeroPadding_apply_image]
    · rw [matrixZeroPadding_not_mem_right e (X * Y) (e p) j hj, Matrix.mul_apply]
      symm
      apply Finset.sum_eq_zero
      intro k _
      rw [matrixZeroPadding_not_mem_right e Y k j hj, mul_zero]
  · rw [matrixZeroPadding_not_mem_left e (X * Y) i j hi, Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro k _
    rw [matrixZeroPadding_not_mem_left e X i k hi, zero_mul]

theorem matrixZeroPadding_star (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) A) :
    matrixZeroPadding e (star X) = star (matrixZeroPadding e X) := by
  ext i j
  change matrixZeroPadding e (star X) i j = star (matrixZeroPadding e X j i)
  by_cases hi : i ∈ Set.range e
  · obtain ⟨p, rfl⟩ := hi
    by_cases hj : j ∈ Set.range e
    · obtain ⟨q, rfl⟩ := hj
      simp only [matrixZeroPadding_apply_image, Matrix.star_apply]
    · rw [matrixZeroPadding_not_mem_right e (star X) (e p) j hj,
        matrixZeroPadding_not_mem_left e X j (e p) hj, star_zero]
  · rw [matrixZeroPadding_not_mem_left e (star X) i j hi,
      matrixZeroPadding_not_mem_right e X j i hi, star_zero]

/-- The algebraic zero-padding map, before assigning the C-star matrix norm. -/
def matrixZeroPaddingHom (e : Fin r ↪ Fin m) :
    Matrix (Fin r) (Fin r) A →⋆ₙₐ[ℂ] Matrix (Fin m) (Fin m) A where
  toFun := matrixZeroPadding e
  map_zero' := by ext i j; simp [matrixZeroPadding]
  map_add' X Y := by
    ext i j
    simp only [matrixZeroPadding, Matrix.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp
  map_smul' c X := by
    ext i j
    simp only [matrixZeroPadding, Matrix.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp
  map_mul' := matrixZeroPadding_mul e
  map_star' := matrixZeroPadding_star e

end AlgebraicPadding

section CStarPadding

variable {A : Type*} [CStarAlgebra A] {r m : ℕ}

/-- Zero padding with the actual C-star matrix norms. -/
def cstarMatrixPadding (e : Fin r ↪ Fin m) :
    CStarMatrix (Fin r) (Fin r) A →⋆ₙₐ[ℂ] CStarMatrix (Fin m) (Fin m) A :=
  CStarMatrix.ofMatrixStarAlgEquiv.toNonUnitalStarAlgHom.comp
    ((matrixZeroPaddingHom e).comp
      CStarMatrix.ofMatrixStarAlgEquiv.symm.toNonUnitalStarAlgHom)

@[simp] theorem cstarMatrixPadding_apply (e : Fin r ↪ Fin m)
    (X : CStarMatrix (Fin r) (Fin r) A) (i j : Fin m) :
    cstarMatrixPadding e X i j = matrixZeroPadding e (CStarMatrix.ofMatrix.symm X) i j := rfl

@[simp] theorem cstarMatrixPadding_apply_image (e : Fin r ↪ Fin m)
    (X : CStarMatrix (Fin r) (Fin r) A) (i j : Fin r) :
    cstarMatrixPadding e X (e i) (e j) = X i j := by
  simp only [cstarMatrixPadding_apply, matrixZeroPadding_apply_image,
    CStarMatrix.ofMatrix_symm_apply]

theorem cstarMatrixPadding_injective (e : Fin r ↪ Fin m) :
    Function.Injective (cstarMatrixPadding (A := A) e) := by
  intro X Y h
  ext i j
  have he := congrArg (fun Z : CStarMatrix (Fin m) (Fin m) A => Z (e i) (e j)) h
  simpa only [cstarMatrixPadding_apply_image] using he

variable [PartialOrder A] [StarOrderedRing A]

/-- No norm or dimension factor is lost by matrix zero padding. -/
@[simp] theorem norm_cstarMatrixPadding (e : Fin r ↪ Fin m)
    (X : CStarMatrix (Fin r) (Fin r) A) : ‖cstarMatrixPadding e X‖ = ‖X‖ :=
  NonUnitalStarAlgHom.norm_map (cstarMatrixPadding e) (cstarMatrixPadding_injective e) X

theorem cstarMatrixPadding_isometry (e : Fin r ↪ Fin m) :
    Isometry (cstarMatrixPadding (A := A) e) :=
  AddMonoidHomClass.isometry_of_norm (cstarMatrixPadding e) (norm_cstarMatrixPadding e)

end CStarPadding

section RepresentedPadding

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {r m : ℕ}

theorem representedPadding_entries (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : Fin r ↪ Fin m) (X : CStarMatrix (Fin r) (Fin r) A) :
    (fun i j => σ (cstarMatrixPadding e X i j)) =
      padOperatorMatrix e (fun i j => σ (X i j)) := by
  apply Matrix.ext
  intro i j
  simp only [cstarMatrixPadding_apply, matrixZeroPadding, padOperatorMatrix,
    map_sum, CStarMatrix.ofMatrix_symm_apply]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> simp

/-- The abstract C-star padding and concrete operator-matrix padding agree. -/
theorem representedMatrixHom_cstarMatrixPadding (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : Fin r ↪ Fin m) (X : CStarMatrix (Fin r) (Fin r) A) :
    representedMatrixHom σ m (cstarMatrixPadding e X) =
      matrixOperator (padOperatorMatrix e (fun i j => σ (X i j))) := by
  change matrixOperator (fun i j => σ (cstarMatrixPadding e X i j)) = _
  rw [representedPadding_entries]

/-- The same identity expressed as extension of the represented operator. -/
theorem representedMatrixHom_cstarMatrixPadding_eq_extension
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (e : Fin r ↪ Fin m)
    (X : CStarMatrix (Fin r) (Fin r) A) :
    representedMatrixHom σ m (cstarMatrixPadding e X) =
      padArrayOperator e (representedMatrixHom σ r X) := by
  rw [representedMatrixHom_cstarMatrixPadding]
  exact matrixOperator_padOperatorMatrix e (fun i j => σ (X i j))

end RepresentedPadding

end KadisonSimilarity

end

end OAI
