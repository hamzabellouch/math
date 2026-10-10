import Mathlib
import OAI.Analysis.WeakInfiniteness.NonUnitalGroupTensor
import OAI.Analysis.WeakInfiniteness.ReducedGroupAlgebra
import OAI.Analysis.WeakInfiniteness.ScalarDiagonal
import OAI.Analysis.WeakInfiniteness.TensorCompression
import OAI.Analysis.WeakInfiniteness.ULiftCStar

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

abbrev ReducedFreeLarge := ULift.{1} (ReducedGroupAlgebra FreeTwo)

def fullToReducedLarge : FullGroupAlgebra (FreeGroup Bool) →⋆ₐ[ℂ] ReducedFreeLarge :=
  uliftStarAlgEquiv.symm.toStarAlgHom.comp fullToReduced

lemma fullToReducedLarge_surjective : Function.Surjective fullToReducedLarge := by
  intro d
  obtain ⟨b,hb⟩ := fullToReduced_surjective d.down
  exact ⟨b, ULift.down_injective hb⟩

def reducedLargeToOperators : ReducedFreeLarge →⋆ₐ[ℂ]
    (GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo) where
  toFun x := x.down.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_one' := rfl
  commutes' _ := rfl
  map_star' _ := rfl

lemma reducedLargeToOperators_injective : Function.Injective reducedLargeToOperators := by
  intro x y h
  exact ULift.down_injective (Subtype.ext h)

lemma reducedLargeToOperators_element (s : FreeTwo) :
    reducedLargeToOperators (fullToReducedLarge (fullGroupElement s)) = leftRegular s := rfl

def freeDiagonalWitness : MinimalTensor (FullGroupAlgebra (FreeGroup Bool)) (FullGroupAlgebra (FreeGroup Bool)) :=
  ∑ s : FreeLetter, minimalElementary (fullGroupElement (freeLetter s)) (fullGroupElement (freeLetter s))

lemma freeDiagonalFunctional_witness : freeDiagonalFunctional freeDiagonalWitness = 4 := by
  simp only [freeDiagonalWitness, map_sum, freeDiagonalFunctional_group_tensors]
  norm_num [FreeLetter]

lemma completion_sum {ι H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K] (s : Finset ι) (T : ι → H →L[ℂ] K) :
    (∑ i ∈ s, T i).completion = ∑ i ∈ s, (T i).completion := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, completion_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, completion_add, ih]

lemma norm_freeDiagonalWitness_reduced_le :
    ‖minimalMapRight (A := FullGroupAlgebra (FreeGroup Bool)) (C := FullGroupAlgebra (FreeGroup Bool)) (D := ReducedFreeLarge) fullToReducedLarge.toNonUnitalStarAlgHom freeDiagonalWitness‖ ≤ 2 * Real.sqrt 3 := by
  let := CStarAlgebra.spectralOrder ReducedFreeLarge
  let := CStarAlgebra.spectralOrderedRing ReducedFreeLarge
  change ‖(minimalMapRight (A := FullGroupAlgebra (FreeGroup Bool)) (C := FullGroupAlgebra (FreeGroup Bool)) (D := ReducedFreeLarge) fullToReducedLarge.toNonUnitalStarAlgHom freeDiagonalWitness).val‖ ≤ _
  apply lp.norm_le_of_forall_le (by positivity)
  intro π
  have he : (minimalMapRight (A := FullGroupAlgebra (FreeGroup Bool)) (C := FullGroupAlgebra (FreeGroup Bool)) (D := ReducedFreeLarge) fullToReducedLarge.toNonUnitalStarAlgHom freeDiagonalWitness).val π =
      (∑ s : FreeLetter, TensorProduct.mapL
        (π.leftRep (fullGroupElement (freeLetter s)))
        (π.rightRep (fullToReducedLarge (fullGroupElement (freeLetter s))))).completion := by
    rw [completion_sum]
    change (∑ s : FreeLetter, spatialElementary (fullGroupElement (freeLetter s))
      (fullToReducedLarge (fullGroupElement (freeLetter s)))) π = _
    rfl
  rw [he, norm_completion]
  have h := tensor_norm_le_faithful Finset.univ
    (fun s : FreeLetter => π.leftRep (fullGroupElement (freeLetter s)))
    (fun s : FreeLetter => fullToReducedLarge (fullGroupElement (freeLetter s)))
    reducedLargeToOperators.toNonUnitalStarAlgHom π.rightRep reducedLargeToOperators_injective
  apply h.trans
  change ‖∑ s : FreeLetter, TensorProduct.mapL (π.leftRep (fullGroupElement (freeLetter s)))
    (leftRegular (freeLetter s) : GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo)‖ ≤ _
  exact norm_freeTensor_nonunital_sum_le π.leftRep (fullGroupUnitary (G := FreeTwo))

end WeakPureInfiniteness
end

end OAI
