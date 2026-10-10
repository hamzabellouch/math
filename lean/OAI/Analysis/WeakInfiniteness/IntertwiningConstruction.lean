import Mathlib
import OAI.Analysis.WeakInfiniteness.IntertwiningLimit

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
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open Filter Topology

universe u v

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def FiniteIntertwining (φ : A →⋆ₙₐ[ℂ] B) : Prop :=
  ∀ (E : Finset A) (F : Finset B) (ε : ℝ), 0 < ε →
    ∃ β : B ≃⋆ₐ[ℂ] B,
      (∀ a ∈ E, dist (β (φ a)) (φ a) < ε) ∧
      ∀ b ∈ F, ∃ a : A, dist (β (φ a)) b < ε

structure IntertwiningState (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] where
  automorphism : B ≃⋆ₐ[ℂ] B
  tests : Finset A

def IntertwiningState.map (φ : A →⋆ₙₐ[ℂ] B) (p : IntertwiningState A B) : A →⋆ₙₐ[ℂ] B :=
  p.automorphism.toNonUnitalStarAlgHom.comp φ

def IntertwiningStep (φ : A →⋆ₙₐ[ℂ] B) (d : ℕ → A) (b : ℕ → B) (n : ℕ)
    (p q : IntertwiningState A B) : Prop :=
  p.tests ⊆ q.tests ∧ d n ∈ q.tests ∧
    (∀ a ∈ p.tests, dist (p.map φ a) (q.map φ a) ≤ (1/2 : ℝ)^n) ∧
    ∀ i ≤ n, ∃ a ∈ q.tests, dist (q.map φ a) (b i) ≤ (1/2 : ℝ)^n

lemma exists_intertwiningStep (φ : A →⋆ₙₐ[ℂ] B) (h : FiniteIntertwining φ)
    (d : ℕ → A) (b : ℕ → B) (n : ℕ) (p : IntertwiningState A B) :
    ∃ q, IntertwiningStep φ d b n p q := by
  classical
  let F : Finset B := Finset.univ.image (fun i : Fin (n+1) => p.automorphism.symm (b i))
  obtain ⟨β,hβ,hF⟩ := h p.tests F ((1/2 : ℝ)^n) (by positivity)
  have hc : ∀ i : Fin (n+1), ∃ a : A,
      dist (p.automorphism (β (φ a))) (b i) ≤ (1/2 : ℝ)^n := by
    intro i
    obtain ⟨a,ha⟩ := hF (p.automorphism.symm (b i)) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    refine ⟨a,?_⟩
    have he := (StarAlgEquiv.isometry p.automorphism).dist_eq (β (φ a)) (p.automorphism.symm (b i))
    rw [p.automorphism.apply_symm_apply] at he
    exact he.trans_le ha.le
  choose c hc using hc
  let E := p.tests ∪ {d n} ∪ Finset.univ.image c
  let q : IntertwiningState A B := ⟨β.trans p.automorphism,E⟩
  refine ⟨q,?_,?_,?_,?_⟩
  · intro a ha
    exact Finset.mem_union_left _ (Finset.mem_union_left _ ha)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  · intro a ha
    change dist (p.automorphism (φ a)) (p.automorphism (β (φ a))) ≤ _
    rw [(StarAlgEquiv.isometry p.automorphism).dist_eq,dist_comm]
    exact (hβ a ha).le
  · intro i hi
    let j : Fin (n+1) := ⟨i,Nat.lt_succ_of_le hi⟩
    refine ⟨c j,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩),hc j⟩

def intertwiningStages (φ : A →⋆ₙₐ[ℂ] B) (h : FiniteIntertwining φ)
    (d : ℕ → A) (b : ℕ → B) : ℕ → IntertwiningState A B :=
  Nat.rec ⟨StarAlgEquiv.refl ℂ B,∅⟩
    (fun n p => Classical.choose (exists_intertwiningStep φ h d b n p))

lemma intertwiningStages_step (φ : A →⋆ₙₐ[ℂ] B) (h : FiniteIntertwining φ)
    (d : ℕ → A) (b : ℕ → B) (n : ℕ) :
    IntertwiningStep φ d b n (intertwiningStages φ h d b n) (intertwiningStages φ h d b (n+1)) :=
  Classical.choose_spec (exists_intertwiningStep φ h d b n (intertwiningStages φ h d b n))

lemma intertwiningStages_tests_mono (φ : A →⋆ₙₐ[ℂ] B) (h : FiniteIntertwining φ)
    (d : ℕ → A) (b : ℕ → B) : Monotone (fun n => (intertwiningStages φ h d b n).tests) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (intertwiningStages_step φ h d b n).1

lemma intertwiningStages_isometry (φ : A →⋆ₙₐ[ℂ] B) (hi : Isometry φ)
    (h : FiniteIntertwining φ) (d : ℕ → A) (b : ℕ → B) (n : ℕ) :
    Isometry ((intertwiningStages φ h d b n).map φ) := by
  change Isometry ((intertwiningStages φ h d b n).automorphism ∘ φ)
  exact (StarAlgEquiv.isometry _).comp hi

lemma intertwiningStages_cauchy_test (φ : A →⋆ₙₐ[ℂ] B) (h : FiniteIntertwining φ)
    (d : ℕ → A) (b : ℕ → B) (N : ℕ) (a : A)
    (ha : a ∈ (intertwiningStages φ h d b N).tests) :
    CauchySeq (fun n => (intertwiningStages φ h d b n).map φ a) := by
  have hc : CauchySeq (fun n => (intertwiningStages φ h d b (N+n)).map φ a) := by
    apply cauchySeq_of_dist_le_of_summable (fun n => (1/2 : ℝ)^(N+n))
    · intro n
      exact (intertwiningStages_step φ h d b (N+n)).2.2.1 a
        (intertwiningStages_tests_mono φ h d b (Nat.le_add_right _ _) ha)
    · exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).comp_injective
        (add_right_injective N)
  apply (cauchySeq_shift N).mp
  simpa only [Nat.add_comm] using hc

lemma intertwiningStages_cauchy (φ : A →⋆ₙₐ[ℂ] B) (hi : Isometry φ)
    (h : FiniteIntertwining φ) (d : ℕ → A) (hd : DenseRange d) (b : ℕ → B) (a : A) :
    CauchySeq (fun n => (intertwiningStages φ h d b n).map φ a) := by
  apply cauchySeq_isometries_of_dense d hd _ (intertwiningStages_isometry φ hi h d b)
  intro i
  exact intertwiningStages_cauchy_test φ h d b (i+1) (d i)
    (intertwiningStages_step φ h d b i).2.1

end

end WeakPureInfiniteness
end

end OAI
