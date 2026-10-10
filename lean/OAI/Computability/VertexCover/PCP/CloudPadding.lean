import Mathlib
import OAI.Computability.VertexCover.PCP.DegreeReplacement
import OAI.Computability.VertexCover.PCP.ExpanderFamily

namespace OAI

                                                                                     

namespace UniqueGames.Foundations.PCP.CloudPadding

open scoped BigOperators
open DegreeReplacement

variable {V E A : Type*}

def paddedSize (k : Nat) : Nat := if k = 0 then 0 else ExpanderFamily.size k

@[simp] theorem paddedSize_zero : paddedSize 0 = 0 := rfl

theorem paddedSize_of_pos {k : Nat} (hk : 0 < k) :
    paddedSize k = ExpanderFamily.size k := by
  simp only [paddedSize, ite_eq_right (Nat.ne_of_gt hk)]

theorem le_paddedSize (k : Nat) : k ≤ paddedSize k := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [paddedSize, ite_eq_right hk]
    exact ExpanderFamily.le_size k

theorem paddedSize_le_mul (k : Nat) : paddedSize k ≤ ExpanderFamily.growth * k := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [paddedSize, ite_eq_right hk]
    exact ExpanderFamily.size_le_mul (Nat.pos_of_ne_zero hk)

def paddedCloudEquiv (G : ConstraintGraph V E A) (dummy : V → Type*) (v : V) :
    Cloud (paddedGraph G dummy) v ≃ Cloud G v ⊕ dummy v where
  toFun := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · exact Sum.inl ⟨e, he⟩
    · change w = v at he
      cases he
      exact Sum.inr d
  invFun := fun z => match z with
    | Sum.inl e => ⟨Sum.inl e.val, e.property⟩
    | Sum.inr d => ⟨Sum.inr ⟨v, d⟩, rfl⟩
  left_inv := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · rfl
    · change w = v at he
      cases he
      rfl
  right_inv := by
    intro z
    cases z <;> rfl

def dartCloudEquiv (G : ConstraintGraph V E A) : E ≃ Σ v : V, Cloud G v where
  toFun e := ⟨G.tail e, ⟨e, rfl⟩⟩
  invFun z := z.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨e, he⟩⟩
    cases he
    rfl

variable [Fintype V] [DecidableEq V] [Fintype E]

theorem sum_card_cloud (G : ConstraintGraph V E A) :
    (∑ v, Fintype.card (Cloud G v)) = Fintype.card E := by
  simpa only [Fintype.card_sigma] using (Fintype.card_congr (dartCloudEquiv G)).symm

theorem card_padded_cloud (G : ConstraintGraph V E A) (dummy : V → Type*)
    [∀ v, Fintype (dummy v)] (v : V) :
    Fintype.card (Cloud (paddedGraph G dummy) v) =
      Fintype.card (Cloud G v) + Fintype.card (dummy v) := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (paddedCloudEquiv G dummy v)

abbrev dummy (G : ConstraintGraph V E A) (v : V) :=
  Fin (paddedSize (Fintype.card (Cloud G v)) - Fintype.card (Cloud G v))

theorem card_cloud (G : ConstraintGraph V E A) (v : V) :
    Fintype.card (Cloud (paddedGraph G (dummy G)) v) =
      paddedSize (Fintype.card (Cloud G v)) := by
  rw [card_padded_cloud]
  simp only [dummy, Fintype.card_fin]
  exact Nat.add_sub_of_le (le_paddedSize _)

omit [Fintype V] in
theorem card_dummy_of_empty (G : ConstraintGraph V E A) (v : V)
    (hk : Fintype.card (Cloud G v) = 0) : Fintype.card (dummy G v) = 0 := by
  simp [dummy, hk]

theorem card_cloud_of_empty (G : ConstraintGraph V E A) (v : V)
    (hk : Fintype.card (Cloud G v) = 0) :
    Fintype.card (Cloud (paddedGraph G (dummy G)) v) = 0 := by
  rw [card_cloud, hk, paddedSize_zero]

theorem card_cloud_eq_family (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    Fintype.card (Cloud (paddedGraph G (dummy G)) v) =
      Fintype.card (ExpanderFamily.Vertex
        (ExpanderFamily.level (Fintype.card (Cloud G v)))) := by
  rw [card_cloud, paddedSize_of_pos hk, ExpanderFamily.card_vertex]
  rfl

theorem card_paddedDart_eq_sum (G : ConstraintGraph V E A) :
    Fintype.card (PaddedDart G (dummy G)) =
      ∑ v, paddedSize (Fintype.card (Cloud G v)) := by
  calc
    Fintype.card (PaddedDart G (dummy G)) =
        ∑ v, Fintype.card (Cloud (paddedGraph G (dummy G)) v) :=
      (sum_card_cloud (paddedGraph G (dummy G))).symm
    _ = ∑ v, paddedSize (Fintype.card (Cloud G v)) := by
      apply Finset.sum_congr rfl
      intro v _
      exact card_cloud G v

theorem card_paddedDart_le (G : ConstraintGraph V E A) :
    Fintype.card (PaddedDart G (dummy G)) ≤ ExpanderFamily.growth * Fintype.card E := by
  rw [card_paddedDart_eq_sum]
  calc
    (∑ v, paddedSize (Fintype.card (Cloud G v))) ≤
        ∑ v, ExpanderFamily.growth * Fintype.card (Cloud G v) := by
      apply Finset.sum_le_sum
      intro v _
      exact paddedSize_le_mul _
    _ = ExpanderFamily.growth * Fintype.card E := by
      rw [← Finset.mul_sum, sum_card_cloud]

end UniqueGames.Foundations.PCP.CloudPadding

end OAI
