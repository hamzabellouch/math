import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace FiniteConstruction
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def Clique {τ : Type} (R : τ → τ → Prop) (s : Finset τ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a ≠ b → R a b
def HasClique {τ : Type} (R : τ → τ → Prop) (s : Finset τ) (n : ℕ) : Prop :=
  ∃ t : Finset τ, t ⊆ s ∧ t.card=n ∧ Clique R t
def orRelation (R : α → α → Prop) (S : β → β → Prop) (x y : α × β) : Prop :=
  R x.1 y.1 ∨ S x.2 y.2

def fiber (J : Finset (α × β)) (a : α) : Finset β :=
  Finset.univ.filter (fun b => (a,b) ∈ J)
omit [Fintype α] in
lemma mem_fiber {J : Finset (α × β)} {a : α} {b : β} : b ∈ fiber J a ↔ (a,b) ∈ J := by
  simp [fiber]
lemma card_fibers (J : Finset (α × β)) : J.card=∑ a, (fiber J a).card := by
  have he : J.card=∑ z : α × β, if z ∈ J then (1 : ℕ) else 0 := by simp
  rw [he,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp only [fiber,Finset.card_filter]

omit [Fintype α] in
lemma join_cliques {R : α → α → Prop} {S : β → β → Prop}
    (hR : ∀ ⦃left right⦄, R left right → R right left)
    {J : Finset (α × β)} {a b : α} (hab : a ≠ b) (hr : R a b)
    {n : ℕ} (ha : HasClique S (fiber J a) n) (hb : HasClique S (fiber J b) n) :
    HasClique (orRelation R S) J (2*n) := by
  classical
  obtain ⟨U,hU,cU,pU⟩ := ha
  obtain ⟨V,hV,cV,pV⟩ := hb
  let U' := U.image (fun x => (a,x))
  let V' := V.image (fun x => (b,x))
  have hdis : Disjoint U' V' := by
    apply Finset.disjoint_left.mpr
    intro z hzU hzV
    obtain ⟨u,hu,heu⟩ := Finset.mem_image.mp hzU
    obtain ⟨v,hv,hev⟩ := Finset.mem_image.mp hzV
    exact hab (congrArg Prod.fst (heu.trans hev.symm))
  refine ⟨U' ∪ V',?_,?_,?_⟩
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
      exact mem_fiber.mp (hU hu)
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      exact mem_fiber.mp (hV hv)
  · rw [Finset.card_union_of_disjoint hdis]
    have hu : U'.card=U.card := Finset.card_image_of_injective _ (fun x y h => (Prod.mk.inj h).2)
    have hv : V'.card=V.card := Finset.card_image_of_injective _ (fun x y h => (Prod.mk.inj h).2)
    rw [hu,hv,cU,cV]
    omega
  · intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
      exact Or.inr (pU u hu v hv (by intro he; subst v; exact hxy rfl))
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
      exact Or.inl hr
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
      exact Or.inl (hR hr)
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
      exact Or.inr (pV u hu v hv (by intro he; subst v; exact hxy rfl))

lemma no_pair_of_no_clique_two {τ : Type} [DecidableEq τ] {R : τ → τ → Prop}
    (hR : ∀ ⦃left right⦄, R left right → R right left)
    {J : Finset τ} (hJ : ¬ HasClique R J 2) :
    ∀ a ∈ J, ∀ b ∈ J, a ≠ b → ¬ R a b := by
  intro a ha b hb hab hr
  apply hJ
  refine ⟨{a,b},by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx; rcases hx with rfl|rfl <;> assumption,?_,?_⟩
  · simp [hab]
  · intro x hx y hy hxy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
    · exact (hxy rfl).elim
    · exact hr
    · exact hR hr
    · exact (hxy rfl).elim

lemma amplification_bound {R : α → α → Prop} {S : β → β → Prop}
    (hR : ∀ ⦃left right⦄, R left right → R right left) (a c t : ℕ)
    (hbase : ∀ G : Finset α, (∀ x ∈ G, ∀ y ∈ G, x ≠ y → ¬ R x y) → G.card ≤ a)
    (htail : ∀ U : Finset β, ¬ HasClique S U t → U.card ≤ c)
    (J : Finset (α × β)) (hJ : ¬ HasClique (orRelation R S) J (2*t)) :
    J.card ≤ a*Fintype.card β+Fintype.card α*c := by
  classical
  let G := Finset.univ.filter (fun x => HasClique S (fiber J x) t)
  have hG : G.card ≤ a := hbase G (by
    intro x hx y hy hxy hrel
    exact hJ (join_cliques hR hxy hrel (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2))
  have hf (x : α) : (fiber J x).card ≤ (if x ∈ G then Fintype.card β else 0)+c := by
    by_cases hx : x ∈ G
    · rw [ite_eq_left hx]
      exact (Finset.card_le_univ _).trans (Nat.le_add_right _ _)
    · rw [ite_eq_right hx,zero_add]
      exact htail _ (by simpa only [G,Finset.mem_filter,Finset.mem_univ,true_and] using hx)
  rw [card_fibers]
  calc
    _ ≤ ∑ x : α, ((if x ∈ G then Fintype.card β else 0)+c) := Finset.sum_le_sum (fun x _ => hf x)
    _ = G.card*Fintype.card β+Fintype.card α*c := by simp [Finset.sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_right _ hG) _
end FiniteConstruction

end

end OAI
