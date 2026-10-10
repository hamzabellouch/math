import OAI.Analysis.KadisonSimilarity.Tracial.FullColumnTheorem

namespace OAI

/-!
# Zero padding of Hilbert arrays

The coordinate inclusion along an arbitrary finite injection is isometric.
Extension of an operator by zero consequently preserves scalar commutator
norms and the norms of their matrix amplifications. No dimension factor occurs.
-/

noncomputable section
namespace KadisonSimilarity

section Coordinates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {r m : ℕ}

/-- The actual zero extension along an injection of finite coordinate sets. -/
def copyEmbeddingMap (e : Fin r ↪ Fin m) :
    HilbertCopies H r →L[ℂ] HilbertCopies H m :=
  ∑ i : Fin r, (copyInsert (e i)).comp (PiLp.proj 2 (fun _ : Fin r => H) i)

@[simp] theorem copyEmbeddingMap_apply_image (e : Fin r ↪ Fin m)
    (x : HilbertCopies H r) (i : Fin r) : copyEmbeddingMap e x (e i) = x i := by
  simp [copyEmbeddingMap, Pi.single_apply, e.injective.eq_iff]

theorem copyEmbeddingMap_apply_of_not_mem (e : Fin r ↪ Fin m)
    (x : HilbertCopies H r) (j : Fin m) (hj : j ∉ Set.range e) :
    copyEmbeddingMap e x j = 0 := by
  have hji (i : Fin r) : j ≠ e i := by
    intro h
    exact hj ⟨i, h.symm⟩
  simp [copyEmbeddingMap, hji]

@[simp] theorem norm_copyEmbeddingMap (e : Fin r ↪ Fin m) (x : HilbertCopies H r) :
    ‖copyEmbeddingMap e x‖ = ‖x‖ := by
  have hs : ‖copyEmbeddingMap e x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    calc
      ∑ j : Fin m, ‖copyEmbeddingMap e x j‖ ^ 2 =
          ∑ j ∈ Finset.univ.map e, ‖copyEmbeddingMap e x j‖ ^ 2 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        have hj' : j ∉ Set.range e := by
          rintro ⟨i, rfl⟩
          exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
        rw [copyEmbeddingMap_apply_of_not_mem e x j hj']
        simp
      _ = ∑ i : Fin r, ‖x i‖ ^ 2 := by
        simp only [Finset.sum_map, copyEmbeddingMap_apply_image]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

/-- Zero extension, now bundled as a linear isometry. -/
def copyEmbedding (e : Fin r ↪ Fin m) :
    HilbertCopies H r →ₗᵢ[ℂ] HilbertCopies H m where
  toLinearMap := (copyEmbeddingMap e).toLinearMap
  norm_map' := norm_copyEmbeddingMap e

@[simp] theorem copyEmbedding_toContinuousLinearMap (e : Fin r ↪ Fin m) :
    (copyEmbedding (H := H) e).toContinuousLinearMap = copyEmbeddingMap e := rfl

theorem norm_copyEmbeddingMap_le (e : Fin r ↪ Fin m) :
    ‖copyEmbeddingMap (H := H) e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [norm_copyEmbeddingMap, one_mul] using (le_refl ‖x‖)

/-- Restriction to the coordinates in the image of the injection. -/
def copyRestriction (e : Fin r ↪ Fin m) :
    HilbertCopies H m →L[ℂ] HilbertCopies H r :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => PiLp.proj 2 (fun _ : Fin m => H) (e i))

@[simp] theorem copyRestriction_apply (e : Fin r ↪ Fin m)
    (x : HilbertCopies H m) (i : Fin r) : copyRestriction e x i = x (e i) := by
  simp [copyRestriction]

theorem norm_copyRestriction_le (e : Fin r ↪ Fin m) :
    ‖copyRestriction (H := H) e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [copyRestriction_apply]
  calc
    ∑ i : Fin r, ‖x (e i)‖ ^ 2 = ∑ j ∈ Finset.univ.map e, ‖x j‖ ^ 2 := by
      rw [Finset.sum_map]
    _ ≤ ∑ j : Fin m, ‖x j‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j _ _
      exact sq_nonneg _

@[simp] theorem copyRestriction_copyEmbedding (e : Fin r ↪ Fin m) :
    (copyRestriction (H := H) e).comp (copyEmbeddingMap e) =
      ContinuousLinearMap.id ℂ (HilbertCopies H r) := by
  ext x i
  simp

theorem copyEmbeddingMap_amplify (e : Fin r ↪ Fin m) (T : H →L[ℂ] H) :
    (copyEmbeddingMap e).comp (amplify T r) =
      (amplify T m).comp (copyEmbeddingMap e) := by
  ext x j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simp
  · simp [copyEmbeddingMap_apply_of_not_mem e _ j hj]

theorem copyRestriction_amplify (e : Fin r ↪ Fin m) (T : H →L[ℂ] H) :
    (copyRestriction e).comp (amplify T m) =
      (amplify T r).comp (copyRestriction e) := by
  ext x i
  simp

end Coordinates

section ContractiveRetraction

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Extension by zero along an isometric, contractively split inclusion has
exactly the original operator norm. -/
theorem norm_split_extension (J : E →L[ℂ] F) (R : F →L[ℂ] E)
    (hJ : ‖J‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hRJ : R.comp J = ContinuousLinearMap.id ℂ E) (T : E →L[ℂ] E) :
    ‖J.comp (T.comp R)‖ = ‖T‖ := by
  have hbound (S : E →L[ℂ] E) : ‖J.comp (S.comp R)‖ ≤ ‖S‖ := by
    calc
      _ ≤ ‖J‖ * (‖S‖ * ‖R‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _))
      _ ≤ 1 * (‖S‖ * 1) := by gcongr
      _ = ‖S‖ := by ring
  apply le_antisymm (hbound T)
  have hrecover : R.comp ((J.comp (T.comp R)).comp J) = T := by
    simp only [← ContinuousLinearMap.comp_assoc, hRJ, ContinuousLinearMap.id_comp]
    simp only [ContinuousLinearMap.comp_assoc, hRJ, ContinuousLinearMap.comp_id]
  calc
    ‖T‖ = ‖R.comp ((J.comp (T.comp R)).comp J)‖ := congrArg norm hrecover.symm
    _ ≤ ‖R‖ * (‖J.comp (T.comp R)‖ * ‖J‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg _))
    _ ≤ 1 * (‖J.comp (T.comp R)‖ * 1) := by gcongr
    _ = ‖J.comp (T.comp R)‖ := by ring

theorem commutator_split_extension (J : E →L[ℂ] F) (R : F →L[ℂ] E)
    (T A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (hJA : J.comp A = B.comp J) (hRB : R.comp B = A.comp R) :
    commutator (J.comp (T.comp R)) B = J.comp ((commutator T A).comp R) := by
  ext x
  have hr := congrArg (fun L : F →L[ℂ] E => L x) hRB
  have hj := congrArg (fun L : E →L[ℂ] F => L (T (R x))) hJA
  simp only [ContinuousLinearMap.comp_apply] at hr hj
  simp only [commutator, sub_apply, mul_apply_eq_comp,
    ContinuousLinearMap.comp_apply, map_sub, hr, ← hj]

end ContractiveRetraction

section Padding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {r m : ℕ}

/-- An operator on the smaller array, extended by zero on all new coordinates. -/
def padArrayOperator (e : Fin r ↪ Fin m)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) :
    HilbertCopies H m →L[ℂ] HilbertCopies H m :=
  (copyEmbeddingMap e).comp (Y.comp (copyRestriction e))

@[simp] theorem norm_padArrayOperator (e : Fin r ↪ Fin m)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) :
    ‖padArrayOperator e Y‖ = ‖Y‖ := by
  unfold padArrayOperator
  exact norm_split_extension
    (E := HilbertCopies H r) (F := HilbertCopies H m)
    (copyEmbeddingMap e) (copyRestriction e)
    (norm_copyEmbeddingMap_le e) (norm_copyRestriction_le e)
    (copyRestriction_copyEmbedding e) Y

/-- Common left multiplication commutes with extending the multiplicity space. -/
theorem commutator_padArrayOperator (e : Fin r ↪ Fin m)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) (T : H →L[ℂ] H) :
    commutator (padArrayOperator e Y) (amplify T m) =
      padArrayOperator e (commutator Y (amplify T r)) :=
  commutator_split_extension _ _ _ _ _ (copyEmbeddingMap_amplify e T)
    (copyRestriction_amplify e T)

/-- Every scalar commutator norm is unchanged by multiplicity padding. -/
theorem norm_commutator_padArrayOperator (e : Fin r ↪ Fin m)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) (T : H →L[ℂ] H) :
    ‖commutator (padArrayOperator e Y) (amplify T m)‖ =
      ‖commutator Y (amplify T r)‖ := by
  rw [commutator_padArrayOperator, norm_padArrayOperator]

/-- In particular, each prescribed homogeneous scalar bound transfers with
the same constant, in both directions. -/
theorem scalar_bound_padArrayOperator_iff {A : Type*} [Norm A]
    (σ : A → (H →L[ℂ] H)) (e : Fin r ↪ Fin m)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) (ε : ℝ) :
    (∀ a, ‖commutator (padArrayOperator e Y) (amplify (σ a) m)‖ ≤ ε * ‖a‖) ↔
      (∀ a, ‖commutator Y (amplify (σ a) r)‖ ≤ ε * ‖a‖) := by
  simp only [norm_commutator_padArrayOperator]

/-- The natural initial-coordinate inclusion is a special case of arbitrary
coordinate padding. -/
def initialCopyEmbedding (hrm : r ≤ m) :
    HilbertCopies H r →ₗᵢ[ℂ] HilbertCopies H m :=
  copyEmbedding (Fin.castLEEmb hrm)

end Padding

section MatrixMultiplicities

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {r m : ℕ}

theorem mapCopies_comp_eq {E F K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (S : F →L[ℂ] K) (T : E →L[ℂ] F) (n : ℕ) :
    mapCopies (S.comp T) n = (mapCopies S n).comp (mapCopies T n) := by
  ext x i
  simp

@[simp] theorem mapCopies_id_eq (n : ℕ) :
    mapCopies (ContinuousLinearMap.id ℂ H) n =
      ContinuousLinearMap.id ℂ (HilbertCopies H n) := by
  ext x i
  simp

theorem amplify_padArrayOperator (e : Fin r ↪ Fin m)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) (n : ℕ) :
    amplify (padArrayOperator e Y) n =
      (mapCopies (copyEmbeddingMap e) n).comp
        ((amplify Y n).comp (mapCopies (copyRestriction e) n)) := by
  ext x i
  simp [padArrayOperator]

/-- Multiplicity padding preserves the norm of every matrix commutator. -/
theorem norm_matrix_commutator_padArrayOperator (e : Fin r ↪ Fin m)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    ‖commutator (amplify (padArrayOperator e Y) n)
      (matrixOperator (fun i j => amplify (X i j) m))‖ =
    ‖commutator (amplify Y n)
      (matrixOperator (fun i j => amplify (X i j) r))‖ := by
  let J := mapCopies (copyEmbeddingMap (H := H) e) n
  let R := mapCopies (copyRestriction (H := H) e) n
  have hJ : ‖J‖ ≤ 1 :=
    (norm_mapCopies_le _ _).trans (norm_copyEmbeddingMap_le e)
  have hR : ‖R‖ ≤ 1 :=
    (norm_mapCopies_le _ _).trans (norm_copyRestriction_le e)
  have hRJ : R.comp J = ContinuousLinearMap.id ℂ (HilbertCopies (HilbertCopies H r) n) := by
    dsimp [R, J]
    rw [← mapCopies_comp_eq, copyRestriction_copyEmbedding, mapCopies_id_eq]
  have hJA : J.comp (matrixOperator (fun i j => amplify (X i j) r)) =
      (matrixOperator (fun i j => amplify (X i j) m)).comp J :=
    mapCopies_intertwines_matrix _ _ _ (fun i j => copyEmbeddingMap_amplify e (X i j))
  have hRB : R.comp (matrixOperator (fun i j => amplify (X i j) m)) =
      (matrixOperator (fun i j => amplify (X i j) r)).comp R :=
    mapCopies_intertwines_matrix _ _ _ (fun i j => copyRestriction_amplify e (X i j))
  rw [amplify_padArrayOperator]
  change ‖commutator (J.comp ((amplify Y n).comp R)) _‖ = _
  rw [commutator_split_extension J R _ _ _ hJA hRB,
    norm_split_extension J R hJ hR hRJ]

end MatrixMultiplicities

section MatrixIndices

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {r m : ℕ}

/-- Entrywise zero extension of a square operator matrix. -/
def padOperatorMatrix (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) (H →L[ℂ] H)) :
    Matrix (Fin m) (Fin m) (H →L[ℂ] H) :=
  fun i j => ∑ p : Fin r, ∑ q : Fin r,
    if i = e p ∧ j = e q then X p q else 0

@[simp] theorem padOperatorMatrix_apply_image (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) (H →L[ℂ] H)) (i j : Fin r) :
    padOperatorMatrix e X (e i) (e j) = X i j := by
  simp [padOperatorMatrix, e.injective.eq_iff, ite_and]

theorem padOperatorMatrix_apply_of_not_mem_left (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) (H →L[ℂ] H)) (i j : Fin m)
    (hi : i ∉ Set.range e) : padOperatorMatrix e X i j = 0 := by
  have h (p : Fin r) : i ≠ e p := fun hp => hi ⟨p, hp.symm⟩
  simp [padOperatorMatrix, h]

theorem padOperatorMatrix_apply_of_not_mem_right (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) (H →L[ℂ] H)) (i j : Fin m)
    (hj : j ∉ Set.range e) : padOperatorMatrix e X i j = 0 := by
  have h (q : Fin r) : j ≠ e q := fun hq => hj ⟨q, hq.symm⟩
  simp [padOperatorMatrix, h]

private theorem sum_eq_sum_embedding {M : Type*} [AddCommMonoid M]
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

/-- Entrywise matrix padding realizes precisely extension by zero. -/
theorem matrixOperator_padOperatorMatrix (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) (H →L[ℂ] H)) :
    matrixOperator (padOperatorMatrix e X) = padArrayOperator e (matrixOperator X) := by
  ext x j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simp only [matrixOperator_apply, padArrayOperator, ContinuousLinearMap.comp_apply,
      copyEmbeddingMap_apply_image]
    rw [sum_eq_sum_embedding e _ (by
      intro j hj
      rw [padOperatorMatrix_apply_of_not_mem_right e X (e i) j hj, zero_apply])]
    simp only [padOperatorMatrix_apply_image, copyRestriction_apply]
  · simp only [matrixOperator_apply, padArrayOperator, ContinuousLinearMap.comp_apply]
    rw [copyEmbeddingMap_apply_of_not_mem e _ j hj]
    apply Finset.sum_eq_zero
    intro i _
    rw [padOperatorMatrix_apply_of_not_mem_left e X j i hj, zero_apply]

/-- Square-matrix padding preserves the concrete operator norm. -/
theorem norm_matrixOperator_padOperatorMatrix (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) (H →L[ℂ] H)) :
    ‖matrixOperator (padOperatorMatrix e X)‖ = ‖matrixOperator X‖ := by
  rw [matrixOperator_padOperatorMatrix, norm_padArrayOperator]

/-- Enlarging the matrix size introduces no loss in a commutator norm. -/
theorem norm_commutator_padOperatorMatrix (e : Fin r ↪ Fin m)
    (Y : H →L[ℂ] H) (X : Matrix (Fin r) (Fin r) (H →L[ℂ] H)) :
    ‖commutator (amplify Y m) (matrixOperator (padOperatorMatrix e X))‖ =
      ‖commutator (amplify Y r) (matrixOperator X)‖ := by
  calc
    _ = ‖commutator (padArrayOperator e (matrixOperator X)) (amplify Y m)‖ := by
      rw [matrixOperator_padOperatorMatrix]
      exact norm_sub_rev
        ((amplify Y m) * (padArrayOperator e (matrixOperator X)))
        ((padArrayOperator e (matrixOperator X)) * (amplify Y m))
    _ = ‖commutator (matrixOperator X) (amplify Y r)‖ :=
      norm_commutator_padArrayOperator e (matrixOperator X) Y
    _ = _ := norm_sub_rev ((matrixOperator X) * (amplify Y r))
      ((amplify Y r) * (matrixOperator X))

/-- Padding the multiplicity and the testing matrix can be performed
independently, preserving the complete commutator test exactly. -/
theorem norm_commutator_pad_both {s t : ℕ}
    (e : Fin r ↪ Fin m) (f : Fin s ↪ Fin t)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r)
    (X : Matrix (Fin s) (Fin s) (H →L[ℂ] H)) :
    ‖commutator (amplify (padArrayOperator e Y) t)
      (matrixOperator (padOperatorMatrix f (fun i j => amplify (X i j) m)))‖ =
    ‖commutator (amplify Y s)
      (matrixOperator (fun i j => amplify (X i j) r))‖ := by
  exact (norm_commutator_padOperatorMatrix (H := HilbertCopies H m) f
    (padArrayOperator e Y) (fun i j => amplify (X i j) m)).trans
      (norm_matrix_commutator_padArrayOperator e Y X)

/-- The inequality used to fit an arbitrary finite test into a common
square array, including the case of zero-size original arrays. -/
theorem norm_commutator_le_square_padding {s t : ℕ}
    (hrm : r ≤ m) (hst : s ≤ t)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r)
    (X : Matrix (Fin s) (Fin s) (H →L[ℂ] H)) :
    ‖commutator (amplify Y s)
      (matrixOperator (fun i j => amplify (X i j) r))‖ ≤
    ‖commutator (amplify (padArrayOperator (Fin.castLEEmb hrm) Y) t)
      (matrixOperator (padOperatorMatrix (Fin.castLEEmb hst)
        (fun i j => amplify (X i j) m)))‖ :=
  le_of_eq (norm_commutator_pad_both (Fin.castLEEmb hrm) (Fin.castLEEmb hst) Y X).symm

end MatrixIndices

end KadisonSimilarity

end

end OAI
