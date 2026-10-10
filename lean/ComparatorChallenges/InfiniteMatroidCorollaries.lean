import Mathlib

namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

abbrev D := (m : ℕ) × ((Fin m → Bool) → Bool)
abbrev E0 := D × Bool
abbrev E := ℤ × D

def contractOnto {α : Type*} (M : Matroid α) (C : Set α) : Matroid α :=
  (M.dual ↾ C).dual

def HasPackingCovering {α : Type*} (M₀ M₁ : Matroid α) : Prop :=
  ∃ P C S₀ S₁ I₀ I₁ : Set α,
    Disjoint P C ∧ P ∪ C = M₀.E ∧ M₁.E = M₀.E ∧
    S₀ ⊆ P ∧ S₁ ⊆ P ∧ Disjoint S₀ S₁ ∧
    (M₀ ↾ P).Spanning S₀ ∧ (M₁ ↾ P).Spanning S₁ ∧
    I₀ ⊆ C ∧ I₁ ⊆ C ∧
    (contractOnto M₀ C).Indep I₀ ∧
    (contractOnto M₁ C).Indep I₁ ∧ I₀ ∪ I₁ = C

def bundleAt (n : ℤ) (b : Bool) : ℤ :=
  if n < 0 then (if b then n - 1 else n) else (if b then n else n - 1)

def parityBit (p : Bool) : ℤ := if p then 1 else 0
abbrev Vertex (p : Bool) := {n : ℤ // n % 2 = parityBit p}

def componentMap {α : Type*} {p : Bool} (v : Vertex p) (x : α × Bool) : ℤ × α :=
  (bundleAt v x.2,x.1)

def globalComponentMap (α : Type*) (p : Bool) (x : Vertex p × (α × Bool)) : ℤ × α :=
  componentMap x.1 x.2

noncomputable def componentEquiv (α : Type*) (p : Bool) : (Vertex p × (α × Bool)) ≃ (ℤ × α) :=
  Equiv.ofBijective (globalComponentMap α p) (by
    have bundleAt_bounds (n : ℤ) (b : Bool) : n - 1 ≤ bundleAt n b ∧ bundleAt n b ≤ n := by
      unfold bundleAt
      split_ifs <;> omega
    have bundleAt_injective (n : ℤ) : Function.Injective (bundleAt n) := by
      intro b c h
      cases b <;> cases c <;> simp_all [bundleAt] <;> split_ifs at h <;> omega
    have bundleAt_right (n : ℤ) : ∃ b, bundleAt n b = n := by
      by_cases h : n < 0
      · exact ⟨false,by simp [bundleAt,h]⟩
      · exact ⟨true,by simp [bundleAt,h]⟩
    have bundleAt_left (n : ℤ) : ∃ b, bundleAt n b = n - 1 := by
      by_cases h : n < 0
      · exact ⟨true,by simp [bundleAt,h]⟩
      · exact ⟨false,by simp [bundleAt,h]⟩

    have globalComponentMap_injective :
        Function.Injective (globalComponentMap α p) := by
      rintro ⟨⟨n,hn⟩,d,b⟩ ⟨⟨m,hm⟩,e,c⟩ h
      have hnm : bundleAt n b = bundleAt m c := congrArg Prod.fst h
      have hde : d = e := congrArg Prod.snd h
      have hb := bundleAt_bounds n b
      have hc := bundleAt_bounds m c
      have hnm' : n = m := by omega
      subst m
      have hbc := bundleAt_injective n hnm
      subst e; subst c
      rfl

    have globalComponentMap_surjective :
        Function.Surjective (globalComponentMap α p) := by
      rintro ⟨n,d⟩
      by_cases hn : n % 2 = parityBit p
      · obtain ⟨b,hb⟩ := bundleAt_right n
        exact ⟨(⟨n,hn⟩,d,b),by simp [globalComponentMap,componentMap,hb]⟩
      · have hn' : (n+1) % 2 = parityBit p := by
          cases p <;> simp only [parityBit,Bool.false_eq_true,ite_false,ite_true] at hn ⊢ <;> omega
        obtain ⟨b,hb⟩ := bundleAt_left (n+1)
        exact ⟨(⟨n+1,hn'⟩,d,b),by simp [globalComponentMap,componentMap,hb]⟩
    exact ⟨globalComponentMap_injective, globalComponentMap_surjective⟩)

noncomputable def rayMatroid {α : Type*} (Q : Matroid (α × Bool)) (p : Bool) : Matroid (ℤ × α) :=
  (Matroid.sum' (fun _ : Vertex p ↦ Q)).mapEquiv (componentEquiv α p)

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

theorem partitional_intersection_counterexample :
    Countable E ∧ Infinite E ∧
    ∃ Q : Matroid E0, Q.E = univ ∧ Q.dual = Q ∧ IsUniform Q ∧
      let M₀ := rayMatroid Q false
      let M₁ := rayMatroid Q true
      M₀.E = univ ∧ M₁.E = univ ∧ M₀.dual = M₀ ∧ M₁.dual = M₁ ∧
      IsPartitional M₀ ∧ IsPartitional M₁ ∧
      (∀ I₀ I₁ : Set E, M₀.Indep I₀ → M₁.Indep I₁ → I₀ ∪ I₁ ≠ univ) ∧
      ¬ HasPackingCovering M₀ M₁ ∧ ¬ HasIntersection M₀ M₁ := by
  sorry

theorem separate_covering_packing_counterexamples :
    (∃ (F : Set E) (M : Bool → Matroid E),
      (∀ i, (M i).E = F) ∧ ¬ CoveringConjectureFor F M) ∧
    (∃ (F : Set E) (M : Bool → Matroid E),
      (∀ i, (M i).E = F) ∧ ¬ PackingConjectureFor F M) := by
  sorry

end InfiniteMatroidCounterexample

end OAI
