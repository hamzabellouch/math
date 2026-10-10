import OAI.Probability.SignedSweeps.UnitaryTensorSpan
import OAI.Probability.SignedSweeps.MatrixTwirl

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

abbrev WordSpace (p : ℕ) (C : Type*) := EuclideanSpace ℂ (Fin p → C)

def wordIsometry {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    WordSpace p C ≃ₗᵢ[ℂ] WordSpace p C :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (wordPositionEquiv g)

def wordRepresentation (p : ℕ) (C : Type*) [Fintype C] :
    Representation ℂ (SymmetricGroup p) (WordSpace p C) where
  toFun g := (wordIsometry (C := C) g).toLinearEquiv.toLinearMap
  map_one' := by
    ext f w
    change f (w ∘ (1 : SymmetricGroup p)) = f w
    rfl
  map_mul' := by
    intro g h
    ext f w
    change f (w ∘ (g * h : SymmetricGroup p)) = f ((w ∘ g) ∘ h)
    rfl

@[simp] lemma wordRepresentation_apply {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (f : WordSpace p C) (w : Fin p → C) :
    wordRepresentation p C g f w = f (w ∘ g) := rfl

lemma wordRepresentation_norm {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (f : WordSpace p C) :
    ‖wordRepresentation p C g f‖ = ‖f‖ := (wordIsometry g).norm_map f

abbrev wordMatrixEquiv (p : ℕ) (C : Type*) [Fintype C] :=
  LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin p → C) ℂ)

lemma wordRepresentation_matrix {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    wordMatrixEquiv p C (wordRepresentation p C g) = wordPositionMatrix g := by
  ext w z
  change (Pi.single (M := fun _ => ℂ) z (1 : ℂ)) (w ∘ g) = _
  simp only [wordPositionMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix,
    Matrix.of_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    Pi.single_apply]
  rfl

lemma wordMatrix_intertwining {p : ℕ} {C : Type*} [Fintype C]
    (T : WordSpace p C →ₗ[ℂ] WordSpace p C) :
    Representation.IsIntertwiningMap (wordRepresentation p C) (wordRepresentation p C) T ↔
      wordMatrixEquiv p C T ∈ wordCommutant p C := by
  constructor
  · intro h g
    rw [← wordRepresentation_matrix, ← map_mul, ← map_mul]
    congr 1
    exact LinearMap.ext (fun x => h.isIntertwining g x)
  · intro h
    constructor
    intro g x
    have hg := h g
    rw [← wordRepresentation_matrix, ← map_mul, ← map_mul] at hg
    exact congrArg (fun T : WordSpace p C →ₗ[ℂ] WordSpace p C => T x)
      ((wordMatrixEquiv p C).injective hg)

def wordCommutantEquiv (p : ℕ) (C : Type*) [Fintype C] :
    Representation.IntertwiningMap (wordRepresentation p C) (wordRepresentation p C) ≃ₗ[ℂ]
      wordCommutant p C where
  toFun f := ⟨wordMatrixEquiv p C f.toLinearMap,
    (wordMatrix_intertwining f.toLinearMap).mp ⟨f.isIntertwining _ _⟩⟩
  invFun A := ((wordMatrixEquiv p C).symm A.1).intertwiningMap_of_isIntertwiningMap _ _
    ((wordMatrix_intertwining _).mpr (by
      rw [(wordMatrixEquiv p C).apply_symm_apply]
      exact A.2)).isIntertwining
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    exact (wordMatrixEquiv p C).symm_apply_apply _
  right_inv A := by
    apply Subtype.ext
    exact (wordMatrixEquiv p C).apply_symm_apply _
  map_add' _ _ := by apply Subtype.ext; apply map_add
  map_smul' _ _ := by apply Subtype.ext; apply map_smul

lemma word_multiplicity_le {p : ℕ} {C E : Type*} [Fintype C]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup p) E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (j : Representation.IntertwiningMap ρ (wordRepresentation p C))
    (hj : ∀ x, ‖j x‖ = ‖x‖) :
    finrank ℂ (Representation.IntertwiningMap ρ (wordRepresentation p C)) ≤
      (p + 1) ^ (Fintype.card C * Fintype.card C) := by
  have h := multiplicity_le_commutant ρ (wordRepresentation p C) hρ wordRepresentation_norm j hj
  rw [(wordCommutantEquiv p C).finrank_eq] at h
  exact h.trans wordCommutant_finrank_le

def wordUnitaryHom (p : ℕ) (C : Type*) [Fintype C] :
    Matrix.unitaryGroup C ℂ →* Matrix.unitaryGroup (Fin p → C) ℂ where
  toFun U := ⟨wordTensorMatrix p U.1, by
    rw [Matrix.mem_unitaryGroup_iff]
    change wordTensorMatrix p U.1 * (wordTensorMatrix p U.1).conjTranspose = 1
    rw [← wordTensorMatrix_star, ← wordTensorMatrix_mul]
    have hu : U.1 * U.1.conjTranspose = 1 := U.2.2
    rw [hu, wordTensorMatrix_one]⟩
  map_one' := by apply Subtype.ext; exact wordTensorMatrix_one
  map_mul' U V := by apply Subtype.ext; exact wordTensorMatrix_mul _ _

lemma wordTensor_mem_commutant {p : ℕ} {C : Type*} [Fintype C] (A : Matrix C C ℂ) :
    wordTensorMatrix p A ∈ wordCommutant p C := by
  rw [← span_wordTensorMatrix]
  exact Submodule.subset_span (Set.mem_range_self A)

lemma wordCommutant_mul {p : ℕ} {C : Type*} [Fintype C]
    {A B : Matrix (Fin p → C) (Fin p → C) ℂ}
    (hA : A ∈ wordCommutant p C) (hB : B ∈ wordCommutant p C) :
    A * B ∈ wordCommutant p C := by
  intro g
  calc
    A * B * wordPositionMatrix g = A * (B * wordPositionMatrix g) := mul_assoc _ _ _
    _ = A * (wordPositionMatrix g * B) := by rw [hB]
    _ = wordPositionMatrix g * (A * B) := by rw [← mul_assoc, hA, mul_assoc]

lemma wordUnitary_central {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix (Fin p → C) (Fin p → C) ℂ)
    (hA : ∀ U : Matrix.unitaryGroup C ℂ,
      A * wordTensorMatrix p U.1 = wordTensorMatrix p U.1 * A)
    (B : Matrix (Fin p → C) (Fin p → C) ℂ) (hB : B ∈ wordCommutant p C) :
    A * B = B * A := by
  rw [← span_unitary_wordTensor] at hB
  induction hB using Submodule.span_induction with
  | mem B h => obtain ⟨U, rfl⟩ := h; exact hA U
  | zero => simp
  | add B D _ _ hB hD => simp only [Matrix.mul_add, Matrix.add_mul, hB, hD]
  | smul c B _ hB => simp only [Matrix.mul_smul, Matrix.smul_mul, hB]

end SignedSweeps
end

end OAI
