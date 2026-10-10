import OAI.Probability.SignedSweeps.CoefficientPush

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {p n : ℕ} {k t : J → ℕ}

def blockFiberEquiv (e : (Σ j, Fin (k j)) ≃ Fin p) (j : J) :
    Fin (k j) ≃ {x : Fin p // (e.symm x).1 = j} where
  toFun x := ⟨e ⟨j,x⟩, by simp⟩
  invFun x := cast (congrArg (fun j => Fin (k j)) x.2) (e.symm x.1).2
  left_inv x := by
    apply eq_of_heq
    exact (cast_heq _ _).trans ((Sigma.ext_iff.mp (e.symm_apply_apply ⟨j,x⟩)).2)
  right_inv x := by
    apply Subtype.ext
    change e _ = x.1
    apply e.symm.injective
    simp only [Equiv.symm_apply_apply]
    exact Sigma.ext x.2.symm (by simp)

omit [Fintype J] in
@[simp] lemma blockFiberEquiv_apply (e : (Σ j, Fin (k j)) ≃ Fin p) (j : J)
    (x : Fin (k j)) : (blockFiberEquiv e j x).1 = e ⟨j,x⟩ := rfl

omit [Fintype J] in
lemma blockPermutation_exists (e : (Σ j, Fin (k j)) ≃ Fin p) (g : SymmetricGroup p)
    (hg : g ∈ fiberSubgroup (fun x => (e.symm x).1)) :
    ∃ a, blockPermutation e a = g := by
  change ∀ x, (e.symm (g x)).1 = (e.symm x).1 at hg
  let a := fun j => (blockFiberEquiv e j).symm.permCongr
    (g.subtypePerm (fun x => by change ((e.symm (g x)).1 = j) ↔ _; rw [hg x]))
  refine ⟨a, ?_⟩
  apply Equiv.ext
  intro x
  obtain ⟨⟨j,x⟩,rfl⟩ := e.surjective x
  rw [blockPermutation_apply]
  have he := (blockFiberEquiv e j).apply_symm_apply
    ((g.subtypePerm (fun x => by change ((e.symm (g x)).1 = j) ↔ _; rw [hg x]))
      (blockFiberEquiv e j x))
  exact congrArg Subtype.val he

omit [Fintype J] in
lemma blockPermutation_range (e : (Σ j, Fin (k j)) ≃ Fin p) (g : SymmetricGroup p) :
    g ∈ (blockPermutation e).range ↔ g ∈ fiberSubgroup (fun x => (e.symm x).1) := by
  constructor
  · rintro ⟨a,rfl⟩
    exact blockPermutation_fiber e a
  · exact blockPermutation_exists e g

def BlockInjectionSquare (e : (Σ j, Fin (k j)) ≃ Fin p)
    (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n)
    (ι : ∀ j, Fin (k j) ↪ Fin (t j)) : Prop :=
  ∀ j x, i (e ⟨j,x⟩) = E ⟨j,ι j x⟩

omit [Fintype J] in
lemma blockInjection_route (e : (Σ j, Fin (k j)) ≃ Fin p)
    (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n)
    (ι : ∀ j, Fin (k j) ↪ Fin (t j)) (hs : BlockInjectionSquare e E i ι) (x : Fin p) :
    (E.symm (i x)).1 = (e.symm x).1 := by
  obtain ⟨⟨j,x⟩,rfl⟩ := e.surjective x
  rw [hs]
  simp

omit [Fintype J] in
lemma blockInjection_range (e : (Σ j, Fin (k j)) ≃ Fin p)
    (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n)
    (ι : ∀ j, Fin (k j) ↪ Fin (t j)) (hs : BlockInjectionSquare e E i ι)
    (j : J) (x : Fin (t j)) : E ⟨j,x⟩ ∈ Set.range i ↔ x ∈ Set.range (ι j) := by
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨⟨j',y⟩,rfl⟩ := e.surjective y
    rw [hs] at hy
    have he := E.injective hy
    have hj : j' = j := congrArg Sigma.fst he
    subst j'
    exact ⟨y,eq_of_heq (Sigma.mk.inj_iff.mp he).2⟩
  · rintro ⟨y,rfl⟩
    exact ⟨e ⟨j,y⟩, hs j y⟩

omit [Fintype J] in
lemma viaEmbedding_blockPermutation (e : (Σ j, Fin (k j)) ≃ Fin p)
    (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n)
    (ι : ∀ j, Fin (k j) ↪ Fin (t j)) (hs : BlockInjectionSquare e E i ι)
    (g : ∀ j, SymmetricGroup (k j)) :
    (blockPermutation e g).viaEmbedding i =
      blockPermutation E (fun j => (g j).viaEmbedding (ι j)) := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y,rfl⟩ := hx
    obtain ⟨⟨j,y⟩,rfl⟩ := e.surjective y
    rw [Equiv.Perm.viaEmbedding_apply, blockPermutation_apply, hs, hs,
      blockPermutation_apply, Equiv.Perm.viaEmbedding_apply]
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ x hx]
    obtain ⟨⟨j,y⟩,rfl⟩ := E.surjective x
    rw [blockPermutation_apply, Equiv.Perm.viaEmbedding_apply_of_notMem]
    exact fun hy => hx ((blockInjection_range e E i ι hs j y).mpr hy)

theorem block_coefficient_restriction (e : (Σ j, Fin (k j)) ≃ Fin p)
    (E : (Σ j, Fin (t j)) ≃ Fin n) (i : Fin p ↪ Fin n)
    (ι : ∀ j, Fin (k j) ↪ Fin (t j)) (hs : BlockInjectionSquare e E i ι)
    (f : ∀ j, SymmetricGroup (t j) → ℂ) (g : SymmetricGroup p) :
    coefficientPush (blockPermutation E) (productCoefficient f) (g.viaEmbedding i) =
      coefficientPush (blockPermutation e)
        (productCoefficient (fun j a => f j (a.viaEmbedding (ι j)))) g := by
  by_cases hg : g ∈ fiberSubgroup (fun x => (e.symm x).1)
  · obtain ⟨a,rfl⟩ := blockPermutation_exists e g hg
    rw [viaEmbedding_blockPermutation e E i ι hs,
      coefficientPush_apply _ (blockPermutation_injective E),
      coefficientPush_apply _ (blockPermutation_injective e)]
    rfl
  · rw [coefficientPush_zero, coefficientPush_zero]
    · exact fun ha => hg ((blockPermutation_range e g).mp ha)
    · intro ha
      have hp := (blockPermutation_range E (g.viaEmbedding i)).mp ha
      apply hg
      intro x
      have hh := hp (i x)
      change (E.symm ((g.viaEmbedding i) (i x))).1 = (E.symm (i x)).1 at hh
      rw [Equiv.Perm.viaEmbedding_apply, blockInjection_route e E i ι hs,
        blockInjection_route e E i ι hs] at hh
      exact hh

end SignedSweeps
end

end OAI
