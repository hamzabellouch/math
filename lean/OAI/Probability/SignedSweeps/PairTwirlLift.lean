import OAI.Probability.SignedSweeps.WordBlocks
import OAI.Probability.SignedSweeps.KroneckerHull
import OAI.Probability.SignedSweeps.MatrixHullLift

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module Set
local instance (priority := 2000) pairTwirlLiftColorDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _
variable {C : Type*} [Fintype C]

def pairColorUnitaryHom :
    (Matrix.unitaryGroup C ℂ × Matrix.unitaryGroup C ℂ) →*
      Matrix.unitaryGroup (C ⊕ C) ℂ where
  toFun g := ⟨Matrix.fromBlocks g.1.1 0 0 g.2.1, by
    rw [Matrix.mem_unitaryGroup_iff]
    simp only [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply, mul_zero, zero_mul,
      add_zero, zero_add]
    have hu : g.1.1 * g.1.1.conjTranspose = 1 := g.1.2.2
    have hv : g.2.1 * g.2.1.conjTranspose = 1 := g.2.2.2
    rw [hu, hv]
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]⟩
  map_one' := by
    apply Subtype.ext
    change Matrix.fromBlocks (1 : Matrix C C ℂ) 0 0 1 = 1
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]
  map_mul' g h := by
    apply Subtype.ext
    simp only [Submonoid.coe_mul, Matrix.fromBlocks_multiply, mul_zero, zero_mul,
      add_zero, zero_add, Prod.fst_mul, Prod.snd_mul]

def pairWordUnitaryHom (p : ℕ) :
    (Matrix.unitaryGroup C ℂ × Matrix.unitaryGroup C ℂ) →*
      Matrix.unitaryGroup (Fin p → C ⊕ C) ℂ :=
  (wordUnitaryHom p (C ⊕ C)).comp pairColorUnitaryHom

@[simp] lemma pairWordUnitaryHom_coe (p : ℕ)
    (U V : Matrix.unitaryGroup C ℂ) :
    (pairWordUnitaryHom p (U,V) : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ) =
      wordTensorMatrix p (Matrix.fromBlocks U.1 0 0 V.1) := rfl

lemma pair_tensor_conjugate (p : ℕ) (A B : Matrix C C ℂ)
    (U V : Matrix.unitaryGroup C ℂ) :
    (pairWordUnitaryHom p (U,V) : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ) *
        wordTensorMatrix p (Matrix.fromBlocks A 0 0 B) *
        star (pairWordUnitaryHom p (U,V) : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ) =
      wordTensorMatrix p (Matrix.fromBlocks (U.1 * A * star U.1) 0 0 (V.1 * B * star V.1)) := by
  simp only [pairWordUnitaryHom_coe, Matrix.star_eq_conjTranspose,
    ← wordTensorMatrix_star, ← wordTensorMatrix_mul, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply,
    mul_zero, zero_mul, add_zero, zero_add]

def pairTensorOrbitHull (p : ℕ) (A B : Matrix C C ℂ) :
    Set (MatrixHilbert (Fin p → C ⊕ C)) :=
  closedOrbitHull (matrixConjugationAction (pairWordUnitaryHom p))
    (matrixHilbertEquiv (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)))

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module Set
local instance (priority := 2000) pairTwirlLiftCompressionDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma word_twirl_mem_closedConvexHull {p : ℕ} {C : Type*} [Fintype C]
    {A : Matrix C C ℂ} {B : Matrix (Fin p → C) (Fin p → C) ℂ}
    (hB : matrixHilbertEquiv B ∈ wordTensorOrbitHull p C A) :
    B ∈ closedConvexHull ℝ (Set.range (fun U : Matrix.unitaryGroup C ℂ =>
      wordTensorMatrix p (U.1 * A * star U.1))) := by
  apply matrix_twirl_mem (wordUnitaryHom p C) hB isClosed_closedConvexHull convex_closedConvexHull
  intro U
  apply subset_closedConvexHull
  refine ⟨U, ?_⟩
  change wordTensorMatrix p (U.1 * A * star U.1) =
    wordTensorMatrix p U.1 * wordTensorMatrix p A * star (wordTensorMatrix p U.1)
  simp only [wordTensorMatrix_mul, Matrix.star_eq_conjTranspose, wordTensorMatrix_star]

def pairMatrixCompression {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) :
    MatrixHilbert (Fin p → C ⊕ C) →ₗ[ℝ]
      Matrix ((Fin u → C) × (Fin v → C)) ((Fin u → C) × (Fin v → C)) ℂ where
  toFun X w z := matrixHilbertEquiv.symm X (pairColorWord e w) (pairColorWord e z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma pairMatrixCompression_orbit {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (A B : Matrix C C ℂ)
    (U V : Matrix.unitaryGroup C ℂ) :
    pairMatrixCompression e
      (matrixConjugationAction (pairWordUnitaryHom p) (U,V)
        (matrixHilbertEquiv (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)))) =
    Matrix.kroneckerMap (· * ·) (wordTensorMatrix u (U.1 * A * star U.1))
      (wordTensorMatrix v (V.1 * B * star V.1)) := by
  change pairMatrixCompression e (matrixHilbertEquiv
    ((pairWordUnitaryHom p (U,V) : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ) *
      wordTensorMatrix p (Matrix.fromBlocks A 0 0 B) *
      star (pairWordUnitaryHom p (U,V) : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ))) = _
  rw [pair_tensor_conjugate]
  ext w z
  exact wordTensorMatrix_pairColor e _ _ w z

lemma kronecker_twirl_mem_compression_hull {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (A B : Matrix C C ℂ)
    (D : Matrix (Fin u → C) (Fin u → C) ℂ)
    (E : Matrix (Fin v → C) (Fin v → C) ℂ)
    (hD : matrixHilbertEquiv D ∈ wordTensorOrbitHull u C A)
    (hE : matrixHilbertEquiv E ∈ wordTensorOrbitHull v C B) :
    Matrix.kroneckerMap (· * ·) D E ∈ closedConvexHull ℝ
      (Set.range (fun g => pairMatrixCompression e
        (matrixConjugationAction (pairWordUnitaryHom p) g
          (matrixHilbertEquiv (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)))))) := by
  apply kronecker_closed_hull isClosed_closedConvexHull convex_closedConvexHull
    (S := Set.range (fun U : Matrix.unitaryGroup C ℂ =>
      wordTensorMatrix u (U.1 * A * star U.1)))
    (T := Set.range (fun V : Matrix.unitaryGroup C ℂ =>
      wordTensorMatrix v (V.1 * B * star V.1))) _
    (word_twirl_mem_closedConvexHull hD) (word_twirl_mem_closedConvexHull hE)
  rintro _ ⟨U,rfl⟩ _ ⟨V,rfl⟩
  apply subset_closedConvexHull
  exact ⟨(U,V), pairMatrixCompression_orbit e A B U V⟩

theorem exists_pair_twirl_lift {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (A B : Matrix C C ℂ)
    (D : Matrix (Fin u → C) (Fin u → C) ℂ)
    (E : Matrix (Fin v → C) (Fin v → C) ℂ)
    (hD : matrixHilbertEquiv D ∈ wordTensorOrbitHull u C A)
    (hE : matrixHilbertEquiv E ∈ wordTensorOrbitHull v C B) :
    ∃ M : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ,
      matrixHilbertEquiv M ∈ pairTensorOrbitHull p A B ∧
      pairMatrixCompression e (matrixHilbertEquiv M) = Matrix.kroneckerMap (· * ·) D E := by
  exact matrix_orbitHull_lift (pairWordUnitaryHom p) (pairMatrixCompression e)
    (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B))
    (kronecker_twirl_mem_compression_hull e A B D E hD hE)

lemma matrix_twirl_entry_eq {I G : Type*} [Fintype I] [DecidableEq I] [Group G]
    (ρ : G →* Matrix.unitaryGroup I ℂ) {A B : Matrix I I ℂ}
    (hB : matrixHilbertEquiv B ∈
      closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A))
    (i j k l : I)
    (h : ∀ g, ((ρ g : Matrix I I ℂ) * A * star (ρ g : Matrix I I ℂ)) i j =
      ((ρ g : Matrix I I ℂ) * A * star (ρ g : Matrix I I ℂ)) k l) : B i j = B k l := by
  apply matrix_twirl_mem ρ hB (S := {M | M i j = M k l})
    (isClosed_eq (by fun_prop) (by fun_prop))
  · intro X hX Y hY a b _ _ _
    change a • X i j + b • Y i j = a • X k l + b • Y k l
    rw [hX,hY]
  · exact h

lemma matrix_twirl_entry_zero {I G : Type*} [Fintype I] [DecidableEq I] [Group G]
    (ρ : G →* Matrix.unitaryGroup I ℂ) {A B : Matrix I I ℂ}
    (hB : matrixHilbertEquiv B ∈
      closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A))
    (i j : I)
    (h : ∀ g, ((ρ g : Matrix I I ℂ) * A * star (ρ g : Matrix I I ℂ)) i j = 0) : B i j = 0 := by
  apply matrix_twirl_mem ρ hB (S := {M | M i j = 0})
    (isClosed_eq (by fun_prop) continuous_const)
  · intro X hX Y hY a b _ _ _
    change a • X i j + b • Y i j = 0
    rw [hX,hY,smul_zero,smul_zero,add_zero]
  · exact h

lemma pair_twirl_compression_eq {u v p : ℕ} {C : Type*} [Fintype C]
    {A B : Matrix C C ℂ} {M : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ}
    (hM : matrixHilbertEquiv M ∈ pairTensorOrbitHull p A B)
    (e f : (Fin u ⊕ Fin v) ≃ Fin p) :
    pairMatrixCompression e (matrixHilbertEquiv M) =
      pairMatrixCompression f (matrixHilbertEquiv M) := by
  ext w z
  apply matrix_twirl_entry_eq (pairWordUnitaryHom p) hM
  rintro ⟨U,V⟩
  rw [pair_tensor_conjugate, wordTensorMatrix_pairColor, wordTensorMatrix_pairColor]

lemma pair_twirl_parity_off {p : ℕ} {C : Type*} [Fintype C]
    {A B : Matrix C C ℂ} {M : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ}
    (hM : matrixHilbertEquiv M ∈ pairTensorOrbitHull p A B)
    (w z : Fin p → C ⊕ C) (h : wordEvenSites w ≠ wordEvenSites z) : M w z = 0 := by
  apply matrix_twirl_entry_zero (pairWordUnitaryHom p) hM
  rintro ⟨U,V⟩
  rw [pair_tensor_conjugate]
  exact wordTensorMatrix_parity_off _ _ w z h

end SignedSweeps
end

end OAI
