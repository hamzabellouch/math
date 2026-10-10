import OAI.Probability.SignedSweeps.GroupedCommute
import OAI.Probability.SignedSweeps.PairDecomposition
import OAI.Probability.SignedSweeps.SignedBlockCoefficients

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
local instance (priority := 2000) {C : Type*} (p : ℕ) : DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k : J → ℕ}

lemma groupedWordOperator_one (e : (Σ j, Fin (k j)) ≃ Fin p) :
    groupedWordOperator (C:=C) e (fun _ => 1) = 1 := by
  simp only [groupedWordOperator, map_one, groupedWordMatrix_one]

lemma groupedWordOperator_sum (e : (Σ j, Fin (k j)) ≃ Fin p)
    {T : J → Type*} [∀ j, Fintype (T j)]
    (A : ∀ j, T j → WordSpace (k j) C →ₗ[ℂ] WordSpace (k j) C) :
    groupedWordOperator e (fun j => ∑ t, A j t) =
      ∑ t : ∀ j, T j, groupedWordOperator e (fun j => A j (t j)) := by
  unfold groupedWordOperator
  rw [← map_sum]
  congr 1
  simp only [map_sum]
  ext x y
  simp only [groupedWordMatrix, Matrix.submatrix_apply, piTensorMatrix,
    Matrix.sum_apply]
  exact Fintype.prod_sum _

lemma groupedWordOperator_zero_factor (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, WordSpace (k j) C →ₗ[ℂ] WordSpace (k j) C)
    (j : J) (hj : A j = 0) : groupedWordOperator e A = 0 := by
  have hz : groupedWordMatrix e (fun i => wordMatrixEquiv (k i) C (A i)) = 0 := by
    ext x y
    change (∏ i : J, (wordMatrixEquiv (k i) C (A i)) (groupWordEquiv e x i) (groupWordEquiv e y i)) = 0
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp only [hj, map_zero, Matrix.zero_apply]
  simp only [groupedWordOperator, hz, map_zero]

def blockTypeProjection (e : (Σ j, Fin (k j)) ≃ Fin p) (t : ∀ j, PairType (k j)) :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) :=
  groupedWordOperator e (fun j => (t j).projector C)

def blockEntropy (t : ∀ j, PairType (k j)) : ℝ := ∑ j, (t j).entropy

lemma blockTypeProjection_sum (e : (Σ j, Fin (k j)) ≃ Fin p) :
    (∑ t : ∀ j, PairType (k j), blockTypeProjection (C:=C) e t) = 1 := by
  unfold blockTypeProjection
  rw [← groupedWordOperator_sum e (fun j (t : PairType (k j)) => t.projector C)]
  simp only [pairTypeProjection_sum, groupedWordOperator_one]

lemma blockTypeProjection_positive (e : (Σ j, Fin (k j)) ≃ Fin p) (t : ∀ j, PairType (k j)) :
    (blockTypeProjection (C:=C) e t).IsPositive := groupedPairTypeProjection_positive _ _ _ _

lemma blockTypeProjection_idempotent (e : (Σ j, Fin (k j)) ≃ Fin p) (t : ∀ j, PairType (k j)) :
    blockTypeProjection (C:=C) e t * blockTypeProjection e t = blockTypeProjection e t :=
  groupedPairTypeProjection_idempotent _ _ _ _

lemma blockTypeProjection_global_commute (e : (Σ j, Fin (k j)) ≃ Fin p) (t : ∀ j, PairType (k j))
    {u v : ℕ} (h : u+v=p) (a : Partition u) (b : Partition v) :
    blockTypeProjection e t * pairTypeProjection h a b C =
      pairTypeProjection h a b C * blockTypeProjection e t :=
  groupedPairTypeProjection_global_commute _ _ _ _ _ _ _

lemma blockTypeProjection_coefficient_commute (e : (Σ j, Fin (k j)) ≃ Fin p)
    (t : ∀ j, PairType (k j)) (f : (∀ j, SymmetricGroup (k j)) → ℂ) :
    blockTypeProjection (C:=C) e t * coefficientAction (signedWordRepresentation p C)
      (coefficientPush (blockPermutation e) f) =
    coefficientAction (signedWordRepresentation p C) (coefficientPush (blockPermutation e) f) *
      blockTypeProjection e t := grouped_signed_coefficient_commute _ _ _ _ _

lemma blockTypeProjection_zero_of_height (e : (Σ j, Fin (k j)) ≃ Fin p)
    (t : ∀ j, PairType (k j)) (j : J) (hj : Fintype.card C < (t j).height) :
    blockTypeProjection (C:=C) e t = 0 := by
  apply groupedWordOperator_zero_factor e _ j
  apply pairTypeProjection_zero_of_height
  exact lt_max_iff.mp hj

lemma blockTypeProjection_trace (e : (Σ j, Fin (k j)) ≃ Fin p)
    (t : ∀ j, PairType (k j)) (f : ∀ j, SymmetricGroup (k j) → ℂ) :
    LinearMap.trace ℂ (WordSpace p (C ⊕ C))
      (blockTypeProjection e t * coefficientAction (signedWordRepresentation p C)
        (coefficientPush (blockPermutation e) (productCoefficient f))) =
      ∏ j, LinearMap.trace ℂ (WordSpace (k j) (C ⊕ C))
        ((t j).projector C * coefficientAction (signedWordRepresentation (k j) C) (f j)) :=
  grouped_signed_coefficient_trace _ _ _ _ _

end SignedSweeps
end

end OAI
