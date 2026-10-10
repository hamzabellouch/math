import OAI.Analysis.KadisonKastler.CornerUnitaryExtension
import OAI.Analysis.KadisonKastler.SignedPermutation

namespace OAI

/-! # Finite signed groups in a countable matrix corner

Each finite group acts on the first finitely many matrix summands and as
the identity on their orthogonal complement.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem blockElement_scalar (i j : ℕ) (z : ℂ) :
    F.blockElement i j (z • (1 : E →L[ℂ] E)) = z • F.entry i j := by
  rw [blockElement, map_smul, mul_smul_comm, smul_mul_assoc,
    cornerExtension_one, ← F.zero_zero, F.mul_entry, ite_eq_left rfl, F.mul_entry, ite_eq_left rfl]

/-- The scalar finite-block representation before adjoining the complement. -/
def scalarBlockHom (n : ℕ) : CStarMatrix (Fin n) (Fin n) ℂ →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  (F.finiteBlockHom n).comp
    (CStarMatrix.mapₙₐ (StarAlgHom.ofId ℂ (E →L[ℂ] E)).toNonUnitalStarAlgHom)

theorem scalarBlockHom_apply {n : ℕ} (a : CStarMatrix (Fin n) (Fin n) ℂ) :
    F.scalarBlockHom n a = ∑ i : Fin n, ∑ j : Fin n, a i j • F.entry i j := by
  change (∑ i : Fin n, ∑ j : Fin n,
    F.blockElement i j (algebraMap ℂ (E →L[ℂ] E) (a i j))) = _
  simp only [Algebra.algebraMap_eq_smul_one, F.blockElement_scalar]

theorem scalarBlockHom_one (n : ℕ) :
    F.scalarBlockHom n 1 = F.partialDiagonal (Finset.range n) := by
  rw [F.scalarBlockHom_apply]
  simp only [CStarMatrix.one_apply, ite_smul, one_smul, zero_smul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Fin.sum_univ_eq_sum_range (fun i => F.entry i i) n

/-- The signed matrix representation with the C-star matrix type explicit. -/
def signedCStarRepresentation (n : ℕ) : SignedPermutation (Fin n) →*
    unitary (CStarMatrix (Fin n) (Fin n) ℂ) where
  toFun g := ⟨CStarMatrix.ofMatrix (signedPermutationHom g : Matrix (Fin n) (Fin n) ℂ), by
    change star (signedPermutationHom g : Matrix (Fin n) (Fin n) ℂ) *
        (signedPermutationHom g : Matrix (Fin n) (Fin n) ℂ) = 1 ∧
      (signedPermutationHom g : Matrix (Fin n) (Fin n) ℂ) *
        star (signedPermutationHom g : Matrix (Fin n) (Fin n) ℂ) = 1
    exact (signedPermutationHom g).property⟩
  map_one' := Subtype.ext (congrArg Subtype.val (map_one signedPermutationHom))
  map_mul' g h := Subtype.ext (congrArg Subtype.val (map_mul signedPermutationHom g h))

/-- The actual ambient representation of the finite signed-permutation group. -/
def finiteSignedRepresentation (n : ℕ) : SignedPermutation (Fin n) →*
    unitary (H →L[ℂ] H) :=
  (cornerUnitaryExtension (A := CStarMatrix (Fin n) (Fin n) ℂ)
    (B := H →L[ℂ] H) (F.scalarBlockHom n)).comp (signedCStarRepresentation n)

/-- Its range is a finite subgroup of the ambient unitary group. -/
def finiteSignedGroup (n : ℕ) : Subgroup (unitary (H →L[ℂ] H)) :=
  (F.finiteSignedRepresentation n).range

instance finiteSignedGroup_finite (n : ℕ) : Finite (F.finiteSignedGroup n) :=
  (Set.finite_range _).to_subtype

theorem finiteSignedRepresentation_apply (n : ℕ) (g : SignedPermutation (Fin n)) :
    (F.finiteSignedRepresentation n g : H →L[ℂ] H) =
      (∑ i : Fin n, ∑ j : Fin n, (signedPermutationHom g : Matrix (Fin n) (Fin n) ℂ) i j •
        F.entry i j) + (1 - F.partialDiagonal (Finset.range n)) := by
  change F.scalarBlockHom n _ + (1 - F.scalarBlockHom n 1) = _
  rw [F.scalarBlockHom_apply, F.scalarBlockHom_one]
  rfl

/-- Diagonal signed elements, with identity on the complementary summands. -/
theorem finiteSignedRepresentation_diagonal (n : ℕ) (d : Fin n → ℤˣ) :
    (F.finiteSignedRepresentation n (SemidirectProduct.inl d) : H →L[ℂ] H) =
      (∑ i : Fin n, ((d i : ℤ) : ℂ) • F.entry i i) +
        (1 - F.partialDiagonal (Finset.range n)) := by
  rw [F.finiteSignedRepresentation_apply]
  have h : (signedPermutationHom (SemidirectProduct.inl d) : Matrix (Fin n) (Fin n) ℂ) =
      signDiagonal d := by
    simp [signedPermutationHom, signDiagonalHom, signDiagonalUnitary]
  rw [h]
  simp [signDiagonal, Matrix.diagonal, ite_smul]

/-- Permutations of the finite block, with identity on its complement. -/
theorem finiteSignedRepresentation_permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (F.finiteSignedRepresentation n (SemidirectProduct.inr σ) : H →L[ℂ] H) =
      (∑ i : Fin n, F.entry (σ i) i) + (1 - F.partialDiagonal (Finset.range n)) := by
  rw [F.finiteSignedRepresentation_apply]
  have h : (signedPermutationHom (SemidirectProduct.inr σ) : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.permMatrixHom (R := ℂ) σ := by
    simp [signedPermutationHom, permutationHom, permutationUnitary]
  rw [h]
  simp only [permutationMatrix_apply, ite_smul, one_smul, zero_smul]
  congr 1
  rw [Finset.sum_comm]
  simp

/-- The finite signed groups stay in every algebra containing the original entries. -/
theorem finiteSignedGroup_mem (M : VonNeumannAlgebra H)
    (hF : ∀ i j, F.entry i j ∈ M) (n : ℕ) (u : F.finiteSignedGroup n) :
    (u : H →L[ℂ] H) ∈ M := by
  obtain ⟨g, hg⟩ := u.property
  have hm : (F.finiteSignedRepresentation n g : H →L[ℂ] H) ∈ M := by
    rw [F.finiteSignedRepresentation_apply]
    apply M.add_mem
    · apply M.sum_mem
      intro i _
      apply M.sum_mem
      intro j _
      exact M.toStarSubalgebra.smul_mem (hF i j) _
    · apply M.sub_mem M.one_mem
      exact M.sum_mem (fun i _ => hF i i)
  rwa [hg] at hm

end FullMatrixCorner

end

end KadisonKastler

end OAI
