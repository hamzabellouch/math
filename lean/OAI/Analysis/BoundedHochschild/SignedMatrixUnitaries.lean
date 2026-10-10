import OAI.Analysis.BoundedHochschild.MatrixCommutants

namespace OAI

/-! A finite group of signed permutation unitaries in a matrix system. -/

noncomputable section

open scoped BigOperators

namespace HochschildMatrixSystems
namespace MatrixSystem

variable {M : Type*} [CStarAlgebra M] {n : ℕ} (E : MatrixSystem M n)

def signScalar (b : Bool) : ℂ := if b then -1 else 1

lemma signScalar_xor (a b : Bool) : signScalar (a ^^ b) = signScalar a * signScalar b := by
  cases a <;> cases b <;> norm_num [signScalar]

@[simp] lemma signScalar_star (a : Bool) : star (signScalar a) = signScalar a := by
  cases a <;> simp [signScalar]

def signedPermutation (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) : M :=
  ∑ i, signScalar (s i) • E.entry (σ i) i

lemma signedPermutation_one : E.signedPermutation 1 (fun _ => false) = 1 := by
  simpa only [signedPermutation, signScalar, Bool.false_eq_true, ↓reduceIte,
    one_smul, Equiv.Perm.one_apply] using E.sum_diagonal

lemma signedPermutation_mul (σ τ : Equiv.Perm (Fin n)) (s t : Fin n → Bool) :
    E.signedPermutation σ s * E.signedPermutation τ t =
      E.signedPermutation (σ * τ) (fun i => s (τ i) ^^ t i) := by
  classical
  simp only [signedPermutation, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm,
    E.entry_mul, smul_ite, smul_zero]
  simp [signScalar_xor, Equiv.Perm.mul_apply]

lemma signedPermutation_star (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) :
    star (E.signedPermutation σ s) =
      E.signedPermutation σ⁻¹ (fun i => s (σ⁻¹ i)) := by
  classical
  simp only [signedPermutation, star_sum, star_smul, signScalar_star, E.star_entry]
  apply Fintype.sum_equiv σ _ _
  intro i
  simp

lemma signedPermutation_mem_unitary (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) :
    E.signedPermutation σ s ∈ unitary M := by
  constructor
  · rw [E.signedPermutation_star, E.signedPermutation_mul, inv_mul_cancel]
    simpa using E.signedPermutation_one
  · rw [E.signedPermutation_star, E.signedPermutation_mul, mul_inv_cancel]
    simpa only [Bool.xor_self] using E.signedPermutation_one

def signedPermutationUnitary (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) : unitary M :=
  ⟨E.signedPermutation σ s, E.signedPermutation_mem_unitary σ s⟩

/-- The actual finite subgroup used in the matrix separability homotopy. -/
def signedPermutationGroup : Subgroup (unitary M) where
  carrier := Set.range (fun p : Equiv.Perm (Fin n) × (Fin n → Bool) =>
    E.signedPermutationUnitary p.1 p.2)
  one_mem' := ⟨(1, fun _ => false), Subtype.ext E.signedPermutation_one⟩
  mul_mem' := by
    rintro _ _ ⟨⟨σ, s⟩, rfl⟩ ⟨⟨τ, t⟩, rfl⟩
    exact ⟨(σ * τ, fun i => s (τ i) ^^ t i), Subtype.ext (E.signedPermutation_mul σ τ s t).symm⟩
  inv_mem' := by
    rintro _ ⟨⟨σ, s⟩, rfl⟩
    exact ⟨(σ⁻¹, fun i => s (σ⁻¹ i)), Subtype.ext (E.signedPermutation_star σ s).symm⟩

instance signedPermutationGroup_finite : Finite E.signedPermutationGroup :=
  (Set.finite_range _).to_subtype

lemma signedPermutation_flip (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    E.signedPermutation σ (fun _ => false) -
      E.signedPermutation σ (fun k => decide (k = j)) = (2 : ℂ) • E.entry (σ j) j := by
  classical
  simp only [signedPermutation, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j]
  · simp [signScalar, two_smul]
  · intro k _ hkj
    simp [signScalar, hkj]
  · simp

/-- Signed permutation unitaries linearly span every matrix entry. -/
lemma entry_mem_signedPermutation_span (i j : Fin n) :
    E.entry i j ∈ Submodule.span ℂ
      (Set.range (fun u : E.signedPermutationGroup => ((u : unitary M) : M))) := by
  classical
  let S := Submodule.span ℂ
    (Set.range (fun u : E.signedPermutationGroup => ((u : unitary M) : M)))
  have hmem (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) : E.signedPermutation σ s ∈ S :=
    Submodule.subset_span ⟨⟨E.signedPermutationUnitary σ s, ⟨(σ, s), rfl⟩⟩, rfl⟩
  have hh := S.sub_mem (hmem (Equiv.swap j i) (fun _ => false))
    (hmem (Equiv.swap j i) (fun k => decide (k = j)))
  rw [E.signedPermutation_flip, Equiv.swap_apply_left] at hh
  have h := S.smul_mem (2⁻¹ : ℂ) hh
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul] using h

lemma neg_one_mem_signedPermutationGroup : (-1 : unitary M) ∈ E.signedPermutationGroup := by
  refine ⟨(1, fun _ => true), Subtype.ext ?_⟩
  change E.signedPermutation 1 (fun _ => true) = -1
  simp only [signedPermutation, signScalar, ↓reduceIte, neg_smul, one_smul,
    Equiv.Perm.one_apply, Finset.sum_neg_distrib, E.sum_diagonal]

end MatrixSystem
end HochschildMatrixSystems

end

end OAI
