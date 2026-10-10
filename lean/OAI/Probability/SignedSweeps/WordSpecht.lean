import OAI.Probability.SignedSweeps.WordIsotypic

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def rowColorWord {p : ℕ} {C : Type*} (μ : Partition p)
    (color : Fin (μ.1.colLen 0) ↪ C) : Fin p → C :=
  fun i => color ⟨μ.rowOf i, μ.rowOf_lt i⟩

lemma rowColorWord_stabilizer {p : ℕ} {C : Type*} (μ : Partition p)
    (color : Fin (μ.1.colLen 0) ↪ C) (g : SymmetricGroup p) :
    rowColorWord μ color ∘ g = rowColorWord μ color ↔ g ∈ rowSubgroup μ := by
  constructor
  · intro h x
    exact congrArg Fin.val (color.injective (congrFun h x))
  · intro h
    ext x
    change color _ = color _
    congr 1
    exact Fin.ext (h x)

lemma rowColorWord_column_row {p : ℕ} {C : Type*} (μ : Partition p)
    (color : Fin (μ.1.colLen 0) ↪ C) (c : colSubgroup μ) (a : rowSubgroup μ) :
    rowColorWord μ color ∘ (c.1 * a.1 : SymmetricGroup p) = rowColorWord μ color ↔ c = 1 := by
  rw [rowColorWord_stabilizer]
  constructor
  · intro h
    apply Subtype.ext
    exact mem_row_col_eq_one μ ((rowSubgroup μ).mul_mem_cancel_right a.2 |>.mp h) c.2
  · rintro rfl
    simp

lemma rowColor_specht_coefficient {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p) (color : Fin (μ.1.colLen 0) ↪ C) :
    spechtOrbitIntertwiner μ (wordRepresentation p C)
      (EuclideanSpace.single (rowColorWord μ color) 1) (spechtGenerator μ)
        (rowColorWord μ color) = (Fintype.card (rowSubgroup μ) : ℂ) := by
  change orbitEvaluation (wordRepresentation p C)
    (EuclideanSpace.single (rowColorWord μ color) 1) (polytabloid μ) _ = _
  simp only [polytabloid, map_sum, map_smul, orbitEvaluation_single]
  have hc (c : colSubgroup μ) (a : rowSubgroup μ) :
      (rowColorWord μ color ∘ c.1) ∘ a.1 = rowColorWord μ color ↔ c = 1 :=
    rowColorWord_column_row μ color c a
  simp [wordRepresentation_apply, hc]

theorem specht_occurs_word {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p) (color : Fin (μ.1.colLen 0) ↪ C) :
    Function.Injective (spechtOrbitIntertwiner μ (wordRepresentation p C)
      (EuclideanSpace.single (rowColorWord μ color) 1)) := by
  let := specht_irreducible μ
  apply (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right
  intro h
  have he := congrArg (fun f : Representation.IntertwiningMap (spechtRepresentation μ)
      (wordRepresentation p C) => f (spechtGenerator μ) (rowColorWord μ color)) h
  rw [rowColor_specht_coefficient] at he
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) he

lemma wordTensor_diagonal {p : ℕ} {C : Type*} (x : C → ℂ) :
    wordTensorMatrix p (Matrix.diagonal x) = Matrix.diagonal (fun w => ∏ i, x (w i)) := by
  ext w z
  by_cases h : w = z
  · subst z
    simp [wordTensorMatrix]
  · rw [Matrix.diagonal_apply_ne _ h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)

lemma wordMatrixEquiv_symm {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix (Fin p → C) (Fin p → C) ℂ) :
    (wordMatrixEquiv p C).symm A = A.toEuclideanLin := by
  rfl

lemma word_diagonal_single {p : ℕ} {C : Type*} [Fintype C]
    (x : C → ℂ) (w : Fin p → C) :
    (wordMatrixEquiv p C).symm (wordTensorMatrix p (Matrix.diagonal x))
      (EuclideanSpace.single w 1) = (∏ i, x (w i)) • EuclideanSpace.single w 1 := by
  rw [wordTensor_diagonal, wordMatrixEquiv_symm]
  apply PiLp.ext
  intro z
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct,
    PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  by_cases h : z = w
  · subst z; simp
  · simp [h]

lemma orbitEvaluation_eigen {p : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup p) E) (T : E →ₗ[ℂ] E)
    (hT : ∀ g, T * ρ g = ρ g * T) (x : E) (z : ℂ) (hx : T x = z • x)
    (f : RegularSpace p) : T (orbitEvaluation ρ x f) = z • orbitEvaluation ρ x f := by
  change T (∑ g, f g • ρ g x) = z • ∑ g, f g • ρ g x
  simp only [map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g _
  have hg := congrArg (fun S : E →ₗ[ℂ] E => S x) (hT g)
  change T (ρ g x) = ρ g (T x) at hg
  rw [hg, hx, map_smul, smul_comm]

theorem rowColor_specht_eigen {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p) (color : Fin (μ.1.colLen 0) ↪ C)
    (x : C → ℂ) (v : Specht μ) :
    (wordMatrixEquiv p C).symm (wordTensorMatrix p (Matrix.diagonal x))
      (spechtOrbitIntertwiner μ (wordRepresentation p C)
        (EuclideanSpace.single (rowColorWord μ color) 1) v) =
      (∏ i, x (rowColorWord μ color i)) •
        spechtOrbitIntertwiner μ (wordRepresentation p C)
          (EuclideanSpace.single (rowColorWord μ color) 1) v := by
  apply orbitEvaluation_eigen
  · intro g
    apply (wordMatrixEquiv p C).injective
    change wordMatrixEquiv p C (_ * _) = wordMatrixEquiv p C (_ * _)
    simp only [map_mul, (wordMatrixEquiv p C).apply_symm_apply, wordRepresentation_matrix]
    exact wordTensor_mem_commutant (Matrix.diagonal x) g
  · exact word_diagonal_single x _

end SignedSweeps
end

end OAI
