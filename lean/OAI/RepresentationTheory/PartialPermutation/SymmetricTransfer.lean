import Mathlib
import OAI.RepresentationTheory.PartialPermutation.ReciprocalTransfer
import OAI.RepresentationTheory.PartialPermutation.Equivalences

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation
noncomputable section

def permBlockEquiv {X : Type*} (M : Set X) : Equiv.Perm M ≃* blockSubgroup M where
  toEquiv := Equiv.Perm.subtypeEquivSubtypePerm (fun x => x ∈ M)
  map_mul' f g := by
    apply Subtype.ext
    exact Equiv.Perm.ofSubtype.map_mul f g

def blockSubgroupSnEquiv {X : Type*} [Fintype X] [DecidableEq X] (M : Set X) :
    blockSubgroup M ≃* Equiv.Perm (Fin (Fintype.card M)) :=
  (permBlockEquiv M).symm.trans (Fintype.equivFin M).permCongrHom

lemma inverseDegreeSum_block {X : Type*} [Fintype X] [DecidableEq X] (M : Set X) (u : ℝ) :
    inverseDegreeSum (blockSubgroup M) u =
      inverseDegreeSum (Equiv.Perm (Fin (Fintype.card M))) u :=
  inverseDegreeSum_equiv (blockSubgroupSnEquiv M) u

def SymmetricReciprocalDegreeBoundedStatement : Prop :=
  ∀ u : ℝ, 0 < u →
    BddAbove {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ x = symmetricInverseDegreeSum n u}

def ComplementaryCosetsStatement : Prop :=
  ∀ (n b : ℕ) (_ : 0 < b) (M : Fin b → Set (Fin n)),
    (∀ i, (M i).Nonempty) →
    Pairwise (fun i j => Disjoint (M i) (M j)) → (⋃ i, M i) = Set.univ →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V),
      Representation.IsIrreducible ρ → IsUnitary ρ →
      ∀ (f : Equiv.Perm (Fin n) → ℝ) (B u : ℝ),
      (∀ g, 0 ≤ f g) → mass f ≤ 1 → 0 < u →
      (∀ i, LeftCosetCap f (blockSubgroup (M i)) B) →
      (hsNormSq (complexFourier ρ (fun g => f g)) ≤
        b * B * symmetricDegreeConstant u *
          (Module.finrank ℂ V : ℝ)^(-1+(u+2)/(b : ℝ))) ∧
      (‖LinearMap.toContinuousLinearMap (complexFourier ρ (fun g => f g))‖^2 ≤
        b * B * symmetricDegreeConstant u *
          (Module.finrank ℂ V : ℝ)^(-1+(u+2)/(b : ℝ)))

lemma inverseDegreeSum_block_sum {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I]
    (M : I → Set X) (u : ℝ) :
    (∑ i, inverseDegreeSum (blockSubgroup (M i)) u) =
      ∑ i, symmetricInverseDegreeSum (Fintype.card (M i)) u := by
  apply Finset.sum_congr rfl
  intro i _
  exact inverseDegreeSum_block (M i) u

theorem symmetric_block_degree_transfer {n b : ℕ} (hb : 0 < b)
    (M : Fin b → Set (Fin n)) (hdis : Pairwise (fun i j => Disjoint (M i) (M j)))
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)
    [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (f : Equiv.Perm (Fin n) → ℝ) (B u : ℝ) (hf : ∀ g, 0 ≤ f g) (hu : 0 < u)
    (hcap : ∀ i, LeftCosetCap f (blockSubgroup (M i)) B) :
    hsNormSq (complexFourier ρ (fun g => f g)) ≤
      B * mass f * (Module.finrank ℂ V : ℝ)^(-1 + (u+2)/(b : ℝ)) *
        ∑ i, symmetricInverseDegreeSum (Fintype.card (M i)) u := by
  have h := inverse_degree_sum_transfer ρ (fun i => blockSubgroup (M i)) hb hρ
    (fun i j hij g hg k hk => blockSubgroup_commute (hdis hij) hg hk) f B u hf hu hcap
  rw [inverseDegreeSum_block_sum M u] at h
  exact h

end
end PartialPermutation

end

end OAI
