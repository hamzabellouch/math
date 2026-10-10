import Mathlib

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave

section RootExtension
variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
variable (H : SimpleGraph A) (G : SimpleGraph V)

noncomputable def graphEmbeddings : Finset (A ↪ V) := by
  classical
  exact Finset.univ.filter (fun f => ∀ a b, H.Adj a b → G.Adj (f a) (f b))

noncomputable def rootedEmbeddingFiber (S : Finset A) (ψ : A → V) : Finset (A ↪ V) := by
  classical
  exact (graphEmbeddings H G).filter (fun f => ∀ a ∈ S, f a = ψ a)

variable {H G}

omit [DecidableEq A] [DecidableEq V] in
lemma mem_graphEmbeddings (f : A ↪ V) :
    f ∈ graphEmbeddings H G ↔ ∀ a b, H.Adj a b → G.Adj (f a) (f b) := by
  classical
  simp only [graphEmbeddings, Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_rootedEmbeddingFiber (S : Finset A) (ψ : A → V) (f : A ↪ V) :
    f ∈ rootedEmbeddingFiber H G S ψ ↔
      f ∈ graphEmbeddings H G ∧ ∀ a ∈ S, f a = ψ a := by
  classical
  simp only [rootedEmbeddingFiber, Finset.mem_filter]

omit [Fintype A] in

lemma walk_crosses_finset {a b : A} (p : H.Walk a b) (S : Finset A)
    (ha : a ∈ S) (hb : b ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, H.Adj x y := by
  induction p with
  | nil => exact False.elim (hb ha)
  | @cons a c b hac p ih =>
    by_cases hc : c ∈ S
    · exact ih hc hb
    · exact ⟨a, ha, c, hc, hac⟩

lemma connected_crosses_finset (hH : H.Preconnected) (S : Finset A)
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    ∃ x ∈ S, ∃ y ∉ S, H.Adj x y := by
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hb⟩ := hSc
  obtain ⟨p⟩ := hH a b
  exact walk_crosses_finset p S ha (Finset.mem_compl.mp hb)

lemma root_fiber_fix_one (S : Finset A) (ψ : A → V) (v : A) (hv : v ∉ S) (z : V) :
    ((rootedEmbeddingFiber H G S ψ).filter (fun f => f v = z)) =
      rootedEmbeddingFiber H G (insert v S) (Function.update ψ v z) := by
  classical
  ext f
  simp only [Finset.mem_filter, mem_rootedEmbeddingFiber]
  constructor
  · rintro ⟨⟨hf, hψ⟩, hz⟩
    refine ⟨hf, ?_⟩
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simpa using hz
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem ha hv)]
      exact hψ a ha
  · rintro ⟨hf, hψ⟩
    refine ⟨⟨hf, ?_⟩, ?_⟩
    · intro a ha
      have hh := hψ a (Finset.mem_insert_of_mem ha)
      simpa [Function.update_of_ne (ne_of_mem_of_not_mem ha hv)] using hh
    · simpa using hψ v (Finset.mem_insert_self _ _)

variable [DecidableRel G.Adj]

theorem rootedEmbeddingFiber_le (hH : H.Preconnected) (Δ : ℕ)
    (hΔ : ∀ x : V, (Finset.univ.filter (G.Adj x)).card ≤ Δ)
    (S : Finset A) (hS : S.Nonempty) (ψ : A → V) :
    (rootedEmbeddingFiber H G S ψ).card ≤ Δ ^ Sᶜ.card := by
  classical
  induction hm : Sᶜ.card using Nat.strong_induction_on generalizing S ψ with
  | h m ih =>
    rw [← hm]
    by_cases hzero : Sᶜ.card = 0
    · have hSuniv : S = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro a
        by_contra ha
        have : a ∈ Sᶜ := Finset.mem_compl.mpr ha
        rw [Finset.card_eq_zero.mp hzero] at this
        exact Finset.notMem_empty a this
      rw [hzero, pow_zero]
      apply Finset.card_le_one.mpr
      intro f hf g hg
      apply Function.Embedding.ext
      intro a
      have hf' := (mem_rootedEmbeddingFiber S ψ f).mp hf
      have hg' := (mem_rootedEmbeddingFiber S ψ g).mp hg
      rw [hf'.2 a (by simp [hSuniv]), hg'.2 a (by simp [hSuniv])]
    · have hSc : Sᶜ.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
      obtain ⟨u, hu, v, hv, huv⟩ := connected_crosses_finset hH S hS hSc
      let t : Finset V := Finset.univ.filter (G.Adj (ψ u))
      have ht : ∀ f ∈ rootedEmbeddingFiber H G S ψ, f v ∈ t := by
        intro f hf
        obtain ⟨hf, hr⟩ := (mem_rootedEmbeddingFiber S ψ f).mp hf
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hr u hu]
        exact (mem_graphEmbeddings f).mp hf u v huv
      have hcard : (insert v S)ᶜ.card + 1 = Sᶜ.card := by
        rw [Finset.compl_insert, Finset.card_erase_of_mem (Finset.mem_compl.mpr hv)]
        exact Nat.sub_add_cancel (Finset.card_pos.mpr hSc)
      have hfib : ∀ z ∈ t,
          ((rootedEmbeddingFiber H G S ψ).filter (fun f => f v = z)).card ≤
            Δ ^ (insert v S)ᶜ.card := by
        intro z _
        rw [root_fiber_fix_one S ψ v hv z]
        exact ih (insert v S)ᶜ.card (by omega) (insert v S)
          (Finset.insert_nonempty _ _) (Function.update ψ v z) rfl
      calc
        _ = ∑ z ∈ t, ((rootedEmbeddingFiber H G S ψ).filter (fun f => f v = z)).card :=
          Finset.card_eq_sum_card_fiberwise ht
        _ ≤ ∑ _z ∈ t, Δ ^ (insert v S)ᶜ.card := Finset.sum_le_sum hfib
        _ = t.card * Δ ^ (insert v S)ᶜ.card := by simp
        _ ≤ Δ * Δ ^ (insert v S)ᶜ.card := Nat.mul_le_mul_right _ (hΔ (ψ u))
        _ = Δ ^ Sᶜ.card := by rw [← hcard, pow_succ']

end RootExtension
end SharpTerminalLeave

end
end

end OAI
