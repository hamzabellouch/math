import Mathlib
import OAI.Analysis.Commutator.ProjectionEquivalence
import OAI.Analysis.Commutator.ProjectionAddition

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type*}

lemma orthogonal_sum_projection (e : ι → H →L[ℂ] H)
    (he : ∀ i,IsStarProjection (e i)) (hc : ∀ i j,i≠j → e i*e j=0)
    (s : Finset ι) : IsStarProjection (∑ i∈s,e i) := by
  classical
  constructor
  · change (∑ i∈s,e i)*(∑ i∈s,e i)=∑ i∈s,e i
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum,Finset.sum_eq_single_of_mem i hi]
    · exact (he i).isIdempotentElem.eq
    · intro j hj hne
      exact hc i j hne.symm
  · change star (∑ i∈s,e i)=∑ i∈s,e i
    rw [star_sum]
    exact Finset.sum_congr rfl (fun i _ => (he i).isSelfAdjoint.star_eq)

omit [CompleteSpace H] in
lemma orthogonal_mul_sum_eq_zero (e : ι → H →L[ℂ] H)
    (hc : ∀ i j,i≠j → e i*e j=0) (s : Finset ι) {i : ι} (hi : i∉s) :
    e i*(∑ j∈s,e j)=0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro j hj
  exact hc i j (fun h => hi (h ▸ hj))

lemma Equivalent.finset_sum {M : VonNeumannAlgebra H} (e f : ι → H →L[ℂ] H)
    (he : ∀ i,IsStarProjection (e i)) (hf : ∀ i,IsStarProjection (f i))
    (hec : ∀ i j,i≠j → e i*e j=0) (hfc : ∀ i j,i≠j → f i*f j=0)
    (h : ∀ i,Equivalent M (e i) (f i)) (s : Finset ι) :
    Equivalent M (∑ i∈s,e i) (∑ i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using equivalent_refl M.zero_mem (IsStarProjection.zero _)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (h i).orthogonal_add (he i) (hf i)
      (orthogonal_sum_projection e he hec s) (orthogonal_sum_projection f hf hfc s)
      (orthogonal_mul_sum_eq_zero e hec s hi) (orthogonal_mul_sum_eq_zero f hfc s hi) ih

lemma SubEquivalent.finset_sum {M : VonNeumannAlgebra H} (e f : ι → H →L[ℂ] H)
    (he : ∀ i,IsStarProjection (e i)) (hf : ∀ i,IsStarProjection (f i))
    (hec : ∀ i j,i≠j → e i*e j=0) (hfc : ∀ i j,i≠j → f i*f j=0)
    (h : ∀ i,SubEquivalent M (e i) (f i)) (s : Finset ι) :
    SubEquivalent M (∑ i∈s,e i) (∑ i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using
      subEquivalent_of_le M.zero_mem (IsStarProjection.zero (H →L[ℂ] H)) (le_refl 0)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (h i).orthogonal_add (he i) (hf i)
      (orthogonal_sum_projection e he hec s) (orthogonal_sum_projection f hf hfc s)
      (orthogonal_mul_sum_eq_zero e hec s hi) (orthogonal_mul_sum_eq_zero f hfc s hi) ih

end Kadison.PartialIsometryOrder

end

end
end

end OAI
