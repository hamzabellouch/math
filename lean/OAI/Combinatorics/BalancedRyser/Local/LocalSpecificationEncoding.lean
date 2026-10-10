import OAI.Combinatorics.BalancedRyser.Local.LocalSpecificationProbability

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical

variable {b κ n : ℕ} {α : Type*} [DecidableEq α]

theorem exists_goodSpecification_of_finset
    (u : Position b → α) (I T : Finset (Position b))
    (hTI : T ⊆ I) (hcard : T.card = n) (hinj : Set.InjOn u T)
    (code : Position b → Code b κ) (rank : α → ℕ)
    (hrank : ∀ v ∈ T, ∀ w ∈ T,
      u w ∈ (anchors (code v)).image u → rank (u v) < rank (u w))
    (E : Position b → Code b κ → Prop) (hE : ∀ v ∈ T, E v (code v)) :
    ∃ σ : Fin n → Position b × Code b κ,
      GoodSpecification u I σ ∧
      (∀ k, E (σ k).1 (σ k).2) ∧
      Finset.univ.image (fun k => (σ k).1) = T := by
  let e : Fin n ≃ {v // v ∈ T} :=
    (Fintype.equivFinOfCardEq (show Fintype.card {v // v ∈ T} = n by
      simpa using hcard)).symm
  let σ : Fin n → Position b × Code b κ := fun k => ((e k).val, code (e k).val)
  refine ⟨σ, ?_, ?_, ?_⟩
  · refine ⟨?_, fun k => hTI (e k).property, rank, ?_⟩
    · intro i j hij
      apply e.injective
      apply Subtype.ext
      exact hinj (e i).property (e j).property hij
    · intro i j hij
      exact hrank _ (e i).property _ (e j).property hij
  · intro k
    exact hE _ (e k).property
  · ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk⟩
      exact hk ▸ (e k).property
    · intro hv
      refine ⟨e.symm ⟨v, hv⟩, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)

end
end Balanced.Local.ConditionSpec

end OAI
