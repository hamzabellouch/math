import OAI.Combinatorics.BalancedRyser.Local.InjectionExposureLaw
import OAI.Combinatorics.BalancedRyser.Probability.CountingExposurePosterior

namespace OAI

namespace Balanced.UniformOrderedSubset

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ι] in

theorem restriction_fiber_card_eq (e f g : ι ↪ α) :
    (Finset.univ.filter (fun σ : Equiv.Perm α => e.trans σ.toEmbedding = f)).card =
      (Finset.univ.filter (fun σ : Equiv.Perm α => e.trans σ.toEmbedding = g)).card := by
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair f g f.injective g.injective
  apply Finset.card_equiv (PermutationSubsetLaw.postcompose τ)
  intro σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    apply Function.Embedding.ext
    intro i
    change τ (σ (e i)) = g i
    rw [show σ (e i) = f i from congrArg (fun z : ι ↪ α => z i) h]
    exact hτ i
  · intro h
    apply Function.Embedding.ext
    intro i
    apply τ.injective
    exact (congrArg (fun z : ι ↪ α => z i) h).trans (hτ i).symm

omit [DecidableEq ι] in

theorem expect_restriction (e : ι ↪ α) (g : (ι ↪ α) → ℝ) :
    (𝔼 σ : Equiv.Perm α, g (e.trans σ.toEmbedding)) = 𝔼 f : ι ↪ α, g f := by
  let n := (Finset.univ.filter
    (fun σ : Equiv.Perm α => e.trans σ.toEmbedding = e)).card
  have hn : 0 < n := Finset.card_pos.mpr ⟨Equiv.refl α, by simp⟩
  apply PermutationSubsetLaw.expect_comp_of_fiber_card_eq Finset.univ Finset.univ
    (fun σ : Equiv.Perm α => e.trans σ.toEmbedding) n hn (fun _ _ => Finset.mem_univ _)
  intro f _
  exact restriction_fiber_card_eq e f e

def imageFiberEquiv (C : Finset α) :
    {f : ι ↪ α // Finset.univ.map f = C} ≃ (ι ≃ C) where
  toFun f := Equiv.ofBijective
    (fun i => (⟨f.val i, by
      exact (Finset.ext_iff.mp f.property _).mp
        (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩ : C))
    ⟨fun _ _ h => f.val.injective (congrArg Subtype.val h), by
      intro x
      have hx : x.val ∈ Finset.univ.map f.val :=
        (Finset.ext_iff.mp f.property _).mpr x.property
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hx
      exact ⟨i, Subtype.ext hi⟩⟩
  invFun e := ⟨e.toEmbedding.trans (Function.Embedding.subtype _), by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩⟩
  left_inv f := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv e := by
    apply Equiv.ext
    intro i
    rfl

theorem expect_embedding_by_image (e : ι ↪ α) (g : (ι → α) → ℝ) :
    (𝔼 f : ι ↪ α, g f) =
      𝔼 C ∈ (Finset.univ : Finset α).powersetCard (Fintype.card ι),
        𝔼 c : ι ≃ C, g (fun i => (c i).val) := by
  let R := Finset.univ.map e
  let n := (Finset.univ.filter (fun f : ι ↪ α => Finset.univ.map f = R)).card
  rw [PermutationSubsetLaw.expect_eq_expect_fiber_of_card_eq
    Finset.univ ((Finset.univ : Finset α).powersetCard (Fintype.card ι))
    (fun f : ι ↪ α => Finset.univ.map f) n
    (fun f _ => Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp⟩)
    (by
      intro C hC
      apply InjectionExposureLaw.range_fiber_card_eq C R
      simpa [R] using (Finset.mem_powersetCard.mp hC).2)]
  apply Finset.expect_congr rfl
  intro C _
  rw [CountingExposurePosterior.expect_subtype]
  let t := Finset.univ.filter (fun f : ι ↪ α => Finset.univ.map f = C)
  let E : t ≃ {f : ι ↪ α // Finset.univ.map f = C} :=
    Equiv.subtypeEquivRight (fun f => by simp [t])
  apply Fintype.expect_equiv (E.trans (imageFiberEquiv C))
  intro f
  rfl

theorem expect_permutation_ordered_subset (e : ι ↪ α) (g : (ι → α) → ℝ) :
    (𝔼 σ : Equiv.Perm α, g (fun i => σ (e i))) =
      𝔼 C ∈ (Finset.univ : Finset α).powersetCard (Fintype.card ι),
        𝔼 c : ι ≃ C, g (fun i => (c i).val) := by
  rw [show (𝔼 σ : Equiv.Perm α, g (fun i => σ (e i))) =
    𝔼 f : ι ↪ α, g f from expect_restriction e (fun f => g f)]
  exact expect_embedding_by_image e g

def enumerationEquiv (e : ι ≃ α) : Equiv.Perm α ≃ (ι ≃ α) where
  toFun p := e.trans p
  invFun c := e.symm.trans c
  left_inv p := by ext x; simp
  right_inv c := by ext i; simp

theorem expect_equivalences_eq_permutations (e : ι ≃ α) (g : (ι → α) → ℝ) :
    (𝔼 c : ι ≃ α, g c) =
      𝔼 p : Equiv.Perm α, g (fun i => p (e i)) := by
  symm
  apply Fintype.expect_equiv (enumerationEquiv e)
  intro p
  rfl

end
end Balanced.UniformOrderedSubset

end OAI
