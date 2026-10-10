import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.Diagonal

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I]
attribute [local instance] Classical.propDecidable

abbrev PackExponent (d : I → ℕ) := (Σ i,Fin (d i)) →₀ ℕ
abbrev SortedPackExponent (d : I → ℕ) := ∀ i,{f : Fin (d i) → ℕ // Monotone f}

def sortPackExponent (d : I → ℕ) (m : PackExponent d) : SortedPackExponent d :=
  fun i=>⟨(fun j=>m ⟨i,j⟩) ∘ Tuple.sort (fun j=>m ⟨i,j⟩),Tuple.monotone_sort _⟩

noncomputable def sortedPackRepresentative (d : I → ℕ) (k : SortedPackExponent d) : PackExponent d :=
  Finsupp.equivFunOnFinite.symm (fun ij=> (k ij.1).val ij.2)

lemma sortPack_representative (d : I → ℕ) (k : SortedPackExponent d) :
    sortPackExponent d (sortedPackRepresentative d k)=k := by
  funext i
  apply Subtype.ext
  exact Tuple.unique_monotone (Tuple.monotone_sort (k i).val) (show Monotone ((k i).val ∘ Equiv.refl _) from (k i).property)

lemma tuple_sorted_comp_perm {n : ℕ} (f : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    (f ∘ σ) ∘ Tuple.sort (f ∘ σ)=f ∘ Tuple.sort f := by
  exact Tuple.unique_monotone (σ:= (Tuple.sort (f ∘ σ)).trans σ)
    (Tuple.monotone_sort (f ∘ σ)) (Tuple.monotone_sort f)

omit [Fintype I] in
lemma packExponent_permute_apply (d : I → ℕ) (g : ∀ i,Equiv.Perm (Fin (d i)))
    (m : PackExponent d) (i : I) (j : Fin (d i)) :
    m.mapDomain (packAction (fun i=>Fin (d i)) g) ⟨i,j⟩=m ⟨i,(g i).symm j⟩ := by
  rw [Finsupp.mapDomain_equiv_apply]
  rfl

omit [Fintype I] in
lemma sortPack_permute (d : I → ℕ) (g : ∀ i,Equiv.Perm (Fin (d i))) (m : PackExponent d) :
    sortPackExponent d (m.mapDomain (packAction (fun i=>Fin (d i)) g))=sortPackExponent d m := by
  funext i
  apply Subtype.ext
  change ((fun j=>m.mapDomain (packAction (fun i=>Fin (d i)) g) ⟨i,j⟩) ∘ Tuple.sort _) = _
  simp only [packExponent_permute_apply]
  exact tuple_sorted_comp_perm (fun j=>m ⟨i,j⟩) (g i).symm

lemma packExponent_of_sorted (d : I → ℕ) (m : PackExponent d) :
    (sortedPackRepresentative d (sortPackExponent d m)).mapDomain
      (packAction (fun i=>Fin (d i)) (fun i=>Tuple.sort (fun j=>m ⟨i,j⟩)))=m := by
  ext ⟨i,j⟩
  rw [packExponent_permute_apply]
  change m ⟨i,Tuple.sort (fun j=>m ⟨i,j⟩) ((Tuple.sort (fun j=>m ⟨i,j⟩)).symm j)⟩=_
  rw [Equiv.apply_symm_apply]

lemma sortPack_fibre_finite (d : I → ℕ) (k : SortedPackExponent d) :
    Set.Finite {m : PackExponent d | sortPackExponent d m=k} := by
  apply (Set.finite_range (fun g : ∀ i,Equiv.Perm (Fin (d i))=>
    (sortedPackRepresentative d k).mapDomain (packAction (fun i=>Fin (d i)) g))).subset
  intro m hm
  refine ⟨fun i=>Tuple.sort (fun j=>m ⟨i,j⟩),?_⟩
  rw [←hm]
  exact packExponent_of_sorted d m

omit [Fintype I] in
lemma packExponent_permute_inverse (d : I → ℕ) (g : ∀ i,Equiv.Perm (Fin (d i))) (m : PackExponent d) :
    (m.mapDomain (packAction (fun i=>Fin (d i)) (fun i=>(g i).symm))).mapDomain
      (packAction (fun i=>Fin (d i)) g)=m := by
  ext ⟨i,j⟩
  simp only [packExponent_permute_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
end ElementaryPositivity.RawShuffle

end

end OAI
