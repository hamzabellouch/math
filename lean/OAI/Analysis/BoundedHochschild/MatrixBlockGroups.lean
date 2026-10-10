import OAI.Analysis.BoundedHochschild.HomogeneousTypeI

namespace OAI

/-! Finite unitary groups for finite central partitions of a matrix algebra. -/

noncomputable section

open scoped BigOperators

namespace HochschildMatrixSystems
namespace MatrixSystem

open BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M] {n r : ℕ} (E : MatrixSystem M n)
  (hcomm : ∀ a b : E.commutant, Commute a b)
  (p : Fin r → E.commutant) (hp : ∀ j, IsStarProjection (p j))
  (ho : ∀ i j, i ≠ j → p i * p j = 0) (hs : ∑ j, p j = 1)

include hp in
lemma partition_coe_projection (j : Fin r) : IsStarProjection (p j : M) := by
  constructor
  · exact congrArg Subtype.val (hp j).isIdempotentElem.eq
  · exact congrArg Subtype.val (hp j).isSelfAdjoint.star_eq

include ho in
lemma partition_coe_orthogonal (i j : Fin r) (hij : i ≠ j) :
    (p i : M) * (p j : M) = 0 := congrArg Subtype.val (ho i j hij)

include hs in
lemma partition_coe_sum : ∑ j, (p j : M) = 1 := by
  simpa using congrArg (fun a : E.commutant => (a : M)) hs

def matrixBlockHom : (Fin r → E.signedPermutationGroup) →* unitary M :=
  centralBlockHom (fun j => (p j : M)) (E.partition_coe_projection p hp)
    (fun j => E.commutant_central hcomm (p j)) (E.partition_coe_orthogonal p ho)
    (E.partition_coe_sum p hs) E.signedPermutationGroup.subtype

def matrixBlockSpan : Submodule ℂ M := Submodule.span ℂ
  (Set.range (fun a : Fin r → E.signedPermutationGroup =>
    (E.matrixBlockHom hcomm p hp ho hs a : M)))

lemma matrixBlock_entry_mem_span (j : Fin r) (a b : Fin n) :
    (p j : M) * E.entry a b ∈ E.matrixBlockSpan hcomm p hp ho hs := by
  exact centralBlock_mul_mem_span (fun j => (p j : M)) (E.partition_coe_projection p hp)
    (fun j => E.commutant_central hcomm (p j)) (E.partition_coe_orthogonal p ho)
    (E.partition_coe_sum p hs) E.signedPermutationGroup.subtype j
    ⟨-1, E.neg_one_mem_signedPermutationGroup⟩ rfl (E.entry_mem_signedPermutation_span a b)

lemma matrixBlock_refined_entry_mem_span (q : E.commutant)
    (hq : ∀ j, q * p j = 0 ∨ q * p j = p j) (a b : Fin n) :
    (q : M) * E.entry a b ∈ E.matrixBlockSpan hcomm p hp ho hs := by
  have he : (q : M) * E.entry a b =
      ∑ j, ((q : M) * (p j : M)) * E.entry a b := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, E.partition_coe_sum p hs, mul_one]
  rw [he]
  apply Submodule.sum_mem
  intro j _
  rcases hq j with hj | hj
  · have he := congrArg Subtype.val hj
    change (q : M) * (p j : M) = 0 at he
    rw [he, zero_mul]
    exact Submodule.zero_mem _
  · have he := congrArg Subtype.val hj
    change (q : M) * (p j : M) = (p j : M) at he
    rw [he]
    exact E.matrixBlock_entry_mem_span hcomm p hp ho hs j a b

end MatrixSystem
end HochschildMatrixSystems

end

end OAI
