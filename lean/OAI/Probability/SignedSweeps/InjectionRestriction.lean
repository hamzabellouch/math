import OAI.Probability.SignedSweeps.TensorMultiplicity

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma irreducible_comp_surjective {G H E : Type*} [Monoid G] [Monoid H]
    [AddCommGroup E] [Module ℂ E] [Nontrivial E]
    (ρ : Representation ℂ G E) [ρ.IsIrreducible] (j : H →* G)
    (hj : Function.Surjective j) : Representation.IsIrreducible (ρ.comp j) := by
  have hb : (⊥ : Subrepresentation (ρ.comp j)) ≠ ⊤ := by
    intro he
    exact bot_ne_top (α := Submodule ℂ E) (congrArg Subrepresentation.toSubmodule he)
  let : Nontrivial (Subrepresentation (ρ.comp j)) := ⟨⟨⊥,⊤,hb⟩⟩
  refine ⟨?_⟩
  intro S
  let T : Subrepresentation ρ := {
    toSubmodule := S.toSubmodule
    apply_mem_toSubmodule g x hx := by
      obtain ⟨h,rfl⟩ := hj g
      exact S.apply_mem_toSubmodule h hx }
  rcases eq_bot_or_eq_top T with ht | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun S : Subrepresentation ρ => S.toSubmodule) ht
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun S : Subrepresentation ρ => S.toSubmodule) ht

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_comp_equiv {H : Type*} [Group H] [Fintype H]
    (ρ : Representation ℂ G E) (e : G ≃* H) (f : H → ℂ) :
    coefficientAction (ρ.comp e.symm.toMonoidHom) f =
      coefficientAction ρ (fun g => f (e g)) := by
  unfold coefficientAction
  rw [← Equiv.sum_comp e.toEquiv]
  simp

omit [Fintype G] [FiniteDimensional ℂ E] in
lemma restrictionEligible_range_iff {n : ℕ} (ρ : Representation ℂ G E)
    (i : G →* SymmetricGroup n) (hi : Function.Injective i) (lam : Partition n) :
    RestrictionEligible i.range (ρ.comp (MonoidHom.ofInjective hi).symm.toMonoidHom) lam ↔
      ∃ f : Representation.IntertwiningMap ρ ((spechtRepresentation lam).comp i), f ≠ 0 := by
  let e := MonoidHom.ofInjective hi
  constructor
  · rintro ⟨f,hf⟩
    let k := f.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ
      ((spechtRepresentation lam).comp i) (by
        intro g x
        have he := Representation.IntertwiningMap.isIntertwining _ _ f (e g) x
        change f (ρ (e.symm (e g)) x) = spechtRepresentation lam (e g).1 (f x) at he
        rw [e.symm_apply_apply] at he
        change f (ρ g x) = spechtRepresentation lam (i g) (f x) at he
        exact he)
    refine ⟨k,?_⟩
    intro hk
    apply hf
    apply Representation.IntertwiningMap.ext
    change k.toLinearMap = 0
    exact congrArg (fun z : Representation.IntertwiningMap ρ ((spechtRepresentation lam).comp i) => z.toLinearMap) hk
  · rintro ⟨f,hf⟩
    let k := f.toLinearMap.intertwiningMap_of_isIntertwiningMap
      (ρ.comp e.symm.toMonoidHom) ((spechtRepresentation lam).comp i.range.subtype) (by
        intro g x
        have he := Representation.IntertwiningMap.isIntertwining _ _ f (e.symm g) x
        change f (ρ (e.symm g) x) = spechtRepresentation lam (i (e.symm g)) (f x) at he
        rwa [MonoidHom.apply_ofInjective_symm] at he)
    refine ⟨k,?_⟩
    intro hk
    apply hf
    apply Representation.IntertwiningMap.ext
    change k.toLinearMap = 0
    exact congrArg (fun z : Representation.IntertwiningMap (ρ.comp e.symm.toMonoidHom) ((spechtRepresentation lam).comp i.range.subtype) => z.toLinearMap) hk

theorem positive_injective_restriction {n : ℕ} (ρ : Representation ℂ G E)
    [ρ.IsIrreducible] [Nontrivial E] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (i : G →* SymmetricGroup n) (hi : Function.Injective i)
    (f : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    0 ≤ (LinearMap.trace ℂ E (coefficientAction ρ (fun g => f (i g)))).re ∧
    (finrank ℂ E : ℝ) * (LinearMap.trace ℂ E (coefficientAction ρ (fun g => f (i g)))).re ≤
      ((Fintype.card G : ℝ) / (Fintype.card (SymmetricGroup n) : ℝ)) *
        ∑ lam : Partition n, if
          (∃ F : Representation.IntertwiningMap ρ ((spechtRepresentation lam).comp i), F ≠ 0) then
          (spechtDimension lam : ℝ) *
            (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f)).re
        else 0 := by
  let : Fintype i.range := @Subgroup.instFintypeSubtypeMemOfDecidablePred _ _ i.range
    (fun _ => Classical.propDecidable _) inferInstance
  let e := MonoidHom.ofInjective hi
  let τ : Representation ℂ i.range E := ρ.comp e.symm.toMonoidHom
  let : τ.IsIrreducible := irreducible_comp_surjective ρ e.symm.toMonoidHom e.symm.surjective
  have ht := specht_positive_restriction i.range τ (fun g => hρ (e.symm g)) f hf
  have he : coefficientAction τ (fun g : i.range => f g) =
      coefficientAction ρ (fun g => f (i g)) := coefficientAction_comp_equiv ρ e _
  erw [he] at ht
  have hc : Fintype.card i.range = Fintype.card G := (Fintype.card_congr e.toEquiv).symm
  simp only [hc, τ, e, restrictionEligible_range_iff] at ht
  exact ht

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma viaEmbeddingHom_injective {A B : Type*} [Finite A] (i : A ↪ B) :
    Function.Injective (Equiv.Perm.viaEmbeddingHom i) := by
  intro g h he
  apply Equiv.ext
  intro x
  have hx := congrArg (fun k : Equiv.Perm B => k (i x)) he
  change (g.viaEmbedding i) (i x) = (h.viaEmbedding i) (i x) at hx
  rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply] at hx
  exact i.injective hx

end SignedSweeps
end

end OAI
