import OAI.Combinatorics.InfiniteMatroid.Basic

namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

def IsUniform {α : Type*} (M : Matroid α) : Prop :=
  ∀ X ⊆ M.E, M.Indep X ∨ M.Spanning X

def IsPartitional {α : Type} (M : Matroid α) : Prop :=
  ∃ (ι : Type) (β : ι → Type) (N : ∀ i, Matroid (β i)) (e : (Σ i, β i) ≃ α),
    (∀ i, IsUniform (N i)) ∧ M = (Matroid.sigma N).mapEquiv e

def HasIntersection {α : Type*} (M N : Matroid α) : Prop :=
  ∃ J J₀ J₁ : Set α, M.Indep J ∧ N.Indep J ∧
    Disjoint J₀ J₁ ∧ J₀ ∪ J₁ = J ∧ M.closure J₀ ∪ N.closure J₁ = M.E

def FamilyCovering {α ι : Type*} (F : Set α) (M : ι → Matroid α) : Prop :=
  ∃ I : ι → Set α, (∀ i, (M i).Indep (I i)) ∧ (⋃ i, I i) = F

def FamilyPacking {α ι : Type*} (M : ι → Matroid α) : Prop :=
  ∃ S : ι → Set α, (Pairwise fun i j ↦ Disjoint (S i) (S j)) ∧
    ∀ i, (M i).Spanning (S i)

def CoveringConjectureFor {α ι : Type*} (F : Set α) (M : ι → Matroid α) : Prop :=
  FamilyCovering F M ↔ ∀ Y ⊆ F,
    FamilyPacking (fun i ↦ M i ↾ Y) → FamilyCovering Y (fun i ↦ M i ↾ Y)

def PackingConjectureFor {α ι : Type*} (F : Set α) (M : ι → Matroid α) : Prop :=
  FamilyPacking M ↔ ∀ Y ⊆ F,
    FamilyCovering Y (fun i ↦ contractOnto (M i) Y) →
    FamilyPacking (fun i ↦ contractOnto (M i) Y)

end InfiniteMatroidCounterexample

end OAI
