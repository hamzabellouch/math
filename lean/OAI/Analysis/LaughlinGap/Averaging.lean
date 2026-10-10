import Mathlib

namespace OAI

/-! Averaging. -/

noncomputable section


namespace LaughlinGap.Averaging
open scoped BigOperators InnerProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def coordinates : Matrix ι ι ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (ι × ι) where
  toFun A := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
  invFun x := Matrix.of (fun i j => x (i,j))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq ι] in
lemma coordinates_inner (A B : Matrix ι ι ℝ) :
    inner ℝ (coordinates A) (coordinates B) = (A.transpose * B).trace := by
  change inner ℝ (WithLp.toLp 2 (fun ij : ι × ι => A ij.1 ij.2))
    (WithLp.toLp 2 (fun ij : ι × ι => B ij.1 ij.2)) = _
  simp only [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct,
    Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

noncomputable def invariantSpace (S : StarSubalgebra ℝ (Matrix ι ι ℝ)) :
    Submodule ℝ (EuclideanSpace ℝ (ι × ι)) :=
  S.toSubalgebra.toSubmodule.map coordinates.toLinearMap

noncomputable def average (S : StarSubalgebra ℝ (Matrix ι ι ℝ)) :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ :=
  coordinates.symm.toLinearMap.comp
    ((invariantSpace S).starProjection.toLinearMap.comp coordinates.toLinearMap)

lemma average_mem (S : StarSubalgebra ℝ (Matrix ι ι ℝ)) (A : Matrix ι ι ℝ) :
    average S A ∈ S := by
  have hm := (invariantSpace S).starProjection_apply_mem (coordinates A)
  obtain ⟨B, hB, he⟩ := hm
  have hab : average S A = B := by
    change coordinates.symm ((invariantSpace S).starProjection (coordinates A)) = B
    rw [← he]
    exact coordinates.symm_apply_apply B
  exact hab ▸ hB

lemma average_orthogonal (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    (A : Matrix ι ι ℝ) {B : Matrix ι ι ℝ} (hB : B ∈ S) :
    ((A - average S A).transpose * B).trace = 0 := by
  rw [← coordinates_inner, map_sub]
  have hB' : coordinates B ∈ invariantSpace S := ⟨B, hB, rfl⟩
  have he := (invariantSpace S).starProjection_inner_eq_zero (coordinates A) (coordinates B) hB'
  simpa [average] using he

lemma average_unique (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    (A B : Matrix ι ι ℝ) (hB : B ∈ S)
    (h : ∀ C ∈ S, ((A-B).transpose * C).trace = 0) :
    average S A = B := by
  apply coordinates.injective
  change (invariantSpace S).starProjection (coordinates A) = coordinates B
  apply (invariantSpace S).eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨B, hB, rfl⟩
  · rintro _ ⟨C,hC,rfl⟩
    rw [← map_sub]
    change inner ℝ (coordinates (A-B)) (coordinates C) = 0
    rw [coordinates_inner]
    exact h C hC

lemma average_eq_self (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    {A : Matrix ι ι ℝ} (hA : A ∈ S) : average S A = A := by
  apply average_unique S A A hA
  simp

lemma average_transpose (S : StarSubalgebra ℝ (Matrix ι ι ℝ)) (A : Matrix ι ι ℝ) :
    average S A.transpose = (average S A).transpose := by
  apply average_unique S A.transpose (average S A).transpose
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using (star_mem (average_mem S A) : star (average S A) ∈ S)
  · intro C hC
    have ht : C.transpose ∈ S := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
        using (star_mem hC : star C ∈ S)
    have h := average_orthogonal S A ht
    rw [← Matrix.transpose_sub, Matrix.transpose_transpose]
    rw [← Matrix.trace_transpose, Matrix.transpose_mul] at h
    rw [Matrix.transpose_transpose, Matrix.trace_mul_comm] at h
    exact h

lemma average_isHermitian (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : (average S A).IsHermitian := by
  change (average S A).conjTranspose = average S A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← average_transpose]
  rw [show A.transpose = A from by simpa [Matrix.IsHermitian] using hA]

lemma trace_mul_average (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    (A : Matrix ι ι ℝ) {B : Matrix ι ι ℝ} (hB : B ∈ S) :
    (A * B).trace = (average S A * B).trace := by
  have h := average_orthogonal S A.transpose hB
  rw [average_transpose, ← Matrix.transpose_sub, Matrix.transpose_transpose,
    Matrix.sub_mul, Matrix.trace_sub] at h
  exact sub_eq_zero.mp h

lemma trace_mul_posSemidef {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  let U : Matrix ι ι ℝ := hB.1.eigenvectorUnitary
  have hAU := hA.conjTranspose_mul_mul_same U
  have hdiag : ∀ i, 0 ≤ (U.conjTranspose * A * U) i i := fun i => hAU.diag_nonneg
  have he : (A * B).trace = ((U.conjTranspose * A * U) *
      Matrix.diagonal hB.1.eigenvalues).trace := by
    conv_lhs => arg 1; rhs; rw [hB.1.spectral_theorem]
    change (A * (U * Matrix.diagonal hB.1.eigenvalues * U.conjTranspose)).trace = _
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  rw [he]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hdiag i) (hB.eigenvalues_nonneg i))

lemma cfc_mem (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    {A : Matrix ι ι ℝ} (hA : A ∈ S) (f : ℝ → ℝ) : cfc f A ∈ S := by
  let : IsClosed (S : Set (Matrix ι ι ℝ)) :=
    S.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  exact _root_.cfc_mem (𝕜' := ℝ) f hA

lemma trace_mul_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (A * cfc f A).trace = ∑ i, hA.eigenvalues i * f (hA.eigenvalues i) := by
  have ht (M : Matrix ι ι ℝ) :
      (Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary M).trace = M.trace := by
    rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.star_mul_self_of_mem (SetLike.coe_mem _), one_mul]
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc]
  conv_lhs => arg 1; lhs; rw [hA.spectral_theorem]
  rw [← map_mul, ht, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rfl

lemma cfc_nonnegative {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ x, 0 ≤ f x) : (cfc f A).PosSemidef := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  exact Matrix.posSemidef_diagonal_iff.mpr (fun i => hf _)

theorem average_positive (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : (average S A).PosSemidef := by
  classical
  have hY := average_isHermitian S hA.isHermitian
  rw [hY.posSemidef_iff_eigenvalues_nonneg]
  intro i
  by_contra hn
  have hn : hY.eigenvalues i < 0 := lt_of_not_ge hn
  let f : ℝ → ℝ := fun x => if x = hY.eigenvalues i then 1 else 0
  have hf : ∀ x, 0 ≤ f x := by intro x; dsimp [f]; split_ifs <;> norm_num
  have hpos := trace_mul_posSemidef hA (cfc_nonnegative hY f hf)
  rw [trace_mul_average S A (cfc_mem S (average_mem S A) f), trace_mul_cfc hY] at hpos
  have hle : ∀ j : ι, hY.eigenvalues j * f (hY.eigenvalues j) ≤ 0 := by
    intro j
    dsimp [f]
    split_ifs with he
    · rw [he, mul_one]; exact hn.le
    · simp
  have hstrict : (∑ j, hY.eigenvalues j * f (hY.eigenvalues j)) < 0 := by
    apply Finset.sum_neg' (fun j _ => hle j)
    refine ⟨i, Finset.mem_univ i, ?_⟩
    simpa [f] using hn
  exact (not_lt_of_ge hpos) hstrict

lemma average_trace (S : StarSubalgebra ℝ (Matrix ι ι ℝ)) (A : Matrix ι ι ℝ) :
    (average S A).trace = A.trace := by
  have h := trace_mul_average S A (one_mem S)
  simpa using h.symm

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def adjointMap (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ) :
    Matrix κ κ ℝ →ₗ[ℝ] Matrix ι ι ℝ :=
  coordinates.symm.toLinearMap.comp
    ((coordinates.toLinearMap.comp (F.comp coordinates.symm.toLinearMap)).adjoint.comp
      coordinates.toLinearMap)

omit [DecidableEq ι] [DecidableEq κ] in
lemma adjointMap_inner (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    inner ℝ (coordinates (F A)) (coordinates B) =
      inner ℝ (coordinates A) (coordinates (adjointMap F B)) := by
  let F' := coordinates.toLinearMap.comp (F.comp coordinates.symm.toLinearMap)
  exact (LinearMap.adjoint_inner_right F' (coordinates A) (coordinates B)).symm

theorem average_natural (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    (T : StarSubalgebra ℝ (Matrix κ κ ℝ)) (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (hF : ∀ A ∈ S, F A ∈ T) (hF' : ∀ B ∈ T, adjointMap F B ∈ S)
    (A : Matrix ι ι ℝ) : average T (F A) = F (average S A) := by
  apply average_unique T (F A) (F (average S A)) (hF _ (average_mem S A))
  intro B hB
  rw [← map_sub, ← coordinates_inner, adjointMap_inner, coordinates_inner]
  exact average_orthogonal S A (hF' B hB)

noncomputable def commutator (L : Matrix ι ι ℝ) :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ where
  toFun X := L*X-X*L
  map_add' A B := by simp [mul_add, add_mul]; abel
  map_smul' r A := by simp [smul_sub]

lemma commutator_adjoint (L A B : Matrix ι ι ℝ) :
    inner ℝ (coordinates (commutator L A)) (coordinates B) =
      inner ℝ (coordinates A) (coordinates (commutator L.transpose B)) := by
  simp only [coordinates_inner, commutator, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.transpose_sub, Matrix.transpose_mul, sub_mul, mul_sub, Matrix.trace_sub]
  rw [Matrix.trace_mul_cycle' A.transpose B L.transpose]
  simp only [Matrix.mul_assoc]

noncomputable def rotationCommutant (L : Matrix ι ι ℝ) :
    StarSubalgebra ℝ (Matrix ι ι ℝ) := StarSubalgebra.centralizer ℝ {L}

lemma rotationCommutant_mem (L A : Matrix ι ι ℝ) :
    A ∈ rotationCommutant L ↔ commutator L A = 0 ∧ commutator L.transpose A = 0 := by
  simp only [rotationCommutant, StarSubalgebra.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, commutator,
    LinearMap.coe_mk, AddHom.coe_mk, sub_eq_zero]

omit [DecidableEq ι] in
lemma coordinates_eq_zero_of_inner {B : Matrix ι ι ℝ}
    (h : ∀ A, inner ℝ (coordinates A) (coordinates B) = 0) : B = 0 := by
  have he := inner_self_eq_zero.mp (h B)
  apply coordinates.injective
  simpa using he

lemma commutator_intertwines_adjoint {L : Matrix ι ι ℝ} {M : Matrix κ κ ℝ}
    (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (hF : ∀ A, F (commutator L.transpose A) = commutator M.transpose (F A))
    (B : Matrix κ κ ℝ) :
    commutator L (adjointMap F B) = adjointMap F (commutator M B) := by
  apply sub_eq_zero.mp
  apply coordinates_eq_zero_of_inner
  intro A
  rw [map_sub, inner_sub_right]
  apply sub_eq_zero.mpr
  rw [← adjointMap_inner]
  have hM := commutator_adjoint M.transpose (F A) B
  simp only [Matrix.transpose_transpose] at hM
  rw [← hM, ← hF, adjointMap_inner]
  have he := commutator_adjoint L.transpose A (adjointMap F B)
  simpa only [Matrix.transpose_transpose] using he.symm

lemma map_rotationCommutant {L : Matrix ι ι ℝ} {M : Matrix κ κ ℝ}
    (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (hF : ∀ A, F (commutator L A) = commutator M (F A))
    (hF' : ∀ A, F (commutator L.transpose A) = commutator M.transpose (F A))
    {A : Matrix ι ι ℝ} (hA : A ∈ rotationCommutant L) :
    F A ∈ rotationCommutant M := by
  rw [rotationCommutant_mem] at hA ⊢
  constructor
  · rw [← hF, hA.1, map_zero]
  · rw [← hF', hA.2, map_zero]

theorem rotation_average_natural {L : Matrix ι ι ℝ} {M : Matrix κ κ ℝ}
    (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ)
    (hF : ∀ A, F (commutator L A) = commutator M (F A))
    (hF' : ∀ A, F (commutator L.transpose A) = commutator M.transpose (F A))
    (A : Matrix ι ι ℝ) :
    average (rotationCommutant M) (F A) = F (average (rotationCommutant L) A) := by
  apply average_natural
  · intro B hB
    exact map_rotationCommutant F hF hF' hB
  · intro B hB
    rw [rotationCommutant_mem] at hB ⊢
    constructor
    · rw [commutator_intertwines_adjoint F hF', hB.1, map_zero]
    · have hh : ∀ A, F (commutator L.transpose.transpose A) =
          commutator M.transpose.transpose (F A) := by simpa using hF
      rw [commutator_intertwines_adjoint F hh, hB.2, map_zero]

end LaughlinGap.Averaging

end

end OAI
