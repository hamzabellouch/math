import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.SubtypeSubsetSums

variable {α : Type*}

def forget (s : Finset α) (T : Finset s) : Finset α :=
  T.map (Function.Embedding.subtype (· ∈ s))

@[simp] theorem card_forget (s : Finset α) (T : Finset s) :
    (forget s T).card = T.card := Finset.card_map _

@[simp] theorem mem_forget (s : Finset α) (T : Finset s) (a : s) :
    a.val ∈ forget s T ↔ a ∈ T := by
  simp [forget]

theorem forget_subset (s : Finset α) (T : Finset s) : forget s T ⊆ s := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  exact b.property

@[simp] theorem forget_univ (s : Finset α) :
    forget s Finset.univ = s := by
  rw [forget, Finset.univ_eq_attach, Finset.attach_map_val]

theorem sum_powersetCard {R : Type*} [AddCommMonoid R]
    (s : Finset α) (k : ℕ) (F : Finset α → R) :
    (∑ T ∈ (Finset.univ : Finset s).powersetCard k, F (forget s T)) =
      ∑ T ∈ s.powersetCard k, F T := by
  have hm := Finset.powersetCard_map
    (Function.Embedding.subtype (· ∈ s)) k (Finset.univ : Finset s)
  have hu : (Finset.univ : Finset s).map
      (Function.Embedding.subtype (· ∈ s)) = s := forget_univ s
  rw [hu] at hm
  rw [hm, Finset.sum_map]
  rfl

theorem prod_forget {R : Type*} [CommMonoid R]
    (s : Finset α) (T : Finset s) (c : α → R) :
    (∏ e ∈ forget s T, c e) = ∏ e ∈ T, c e.val := by
  exact Finset.prod_map T (Function.Embedding.subtype (· ∈ s)) c

theorem sum_powersetCard_filter {R : Type*} [AddCommMonoid R]
    (s : Finset α) (k : ℕ) (P : Finset α → Prop) [DecidablePred P]
    (F : Finset α → R) :
    (∑ T ∈ ((Finset.univ : Finset s).powersetCard k).filter (fun T => P (forget s T)),
      F (forget s T)) =
      ∑ T ∈ (s.powersetCard k).filter P, F T := by
  simp only [Finset.sum_filter]
  exact sum_powersetCard s k (fun T => if P T then F T else 0)

end Problem336.SubtypeSubsetSums

end

end OAI
