import Mathlib
import OAI.Computability.VertexCover.Reduction.HonestLargeSumIndependent
import OAI.Computability.VertexCover.Reduction.PairEventMean

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

theorem internalPairs_card {d : ℕ} (J : Finset (Fin d)) :
    (internalPairs J).card = J.card.choose 2 := by
  classical
  rw [← Finset.card_powersetCard]
  apply Finset.card_bij (fun e _ => ({e.1.1, e.1.2} : Finset (Fin d)))
  · intro e he
    have hjk := (Finset.mem_filter.mp he).2
    apply Finset.mem_powersetCard.mpr
    exact ⟨by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using hjk,
      Finset.card_pair (ne_of_lt e.2)⟩
  · intro e he f hf h
    have hj : e.1.1 ∈ ({f.1.1, f.1.2} : Finset (Fin d)) := by rw [← h]; simp
    have hk : e.1.2 ∈ ({f.1.1, f.1.2} : Finset (Fin d)) := by rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj hk
    apply Subtype.ext
    apply Prod.ext
    · rcases hj with hj | hj
      · exact hj
      · rcases hk with hk | hk
        · have := e.2
          rw [hj, hk] at this
          exact False.elim (lt_asymm f.2 this)
        · exact False.elim ((ne_of_lt e.2) (hj.trans hk.symm))
    · rcases hk with hk | hk
      · rcases hj with hj | hj
        · exact False.elim ((ne_of_lt e.2) (hj.trans hk.symm))
        · have := e.2
          rw [hj, hk] at this
          exact False.elim (lt_asymm f.2 this)
      · exact hk
  · intro A hA
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hA
    obtain ⟨j, k, hne, rfl⟩ := Finset.card_eq_two.mp hcard
    have hj := hsub (Finset.mem_insert_self j {k})
    have hk := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self k))
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨⟨(j,k), hlt⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hk⟩
    · refine ⟨⟨(k,j), hgt⟩, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hj⟩
      · simp [Finset.pair_comm]

theorem positionPair_card (d : ℕ) : Fintype.card (PositionPair d) = d.choose 2 := by
  classical
  have h := internalPairs_card (Finset.univ : Finset (Fin d))
  simpa [internalPairs] using h

theorem vertex_card (Φ : LabelCover) (d : ℕ) :
    Fintype.card (Φ.Vertex d) = Φ.M^(d.choose 2) * (2*d+1)^(Φ.WeightDimension d * d) := by
  simp [Vertex, Seeds, positionPair_card, pow_mul]

end VertexCover.LabelCover

namespace VertexCover

theorem finiteMean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : finiteMean f ≤ finiteMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

theorem finiteMean_const {α : Type*} [Fintype α] [Nonempty α] (b : ℝ) :
    finiteMean (fun _ : α => b) = b := by
  simp only [finiteMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_div_cancel_left₀ _ (show (Fintype.card α : ℝ) ≠ 0 from
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt Fintype.card_pos))]

theorem finiteMean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    finiteMean (fun a => f a + g a) = finiteMean f + finiteMean g := by
  simp only [finiteMean, Finset.sum_add_distrib, add_div]

theorem finiteMean_sum {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    finiteMean (fun a => ∑ b, f a b) = ∑ b, finiteMean (fun a => f a b) := by
  unfold finiteMean
  rw [Finset.sum_comm, Finset.sum_div]

theorem finiteMean_one_add_sum {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] (f : α → β → ℝ) :
    finiteMean (fun a => (1 : ℝ) + ∑ b, f a b) =
      1 + ∑ b, finiteMean (fun a => f a b) := by
  rw [finiteMean_add, finiteMean_const, finiteMean_sum]

theorem finiteMean_union_bound {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] (z : α → ℝ) (f : α → β → ℝ) (B : ℝ)
    (hz : ∀ a, z a ≤ 1 + ∑ b, f a b)
    (hf : ∀ b, finiteMean (fun a => f a b) ≤ B) :
    finiteMean z ≤ 1 + Fintype.card β * B := by
  calc
    finiteMean z ≤ finiteMean (fun a => (1 : ℝ) + ∑ b, f a b) := finiteMean_mono hz
    _ = 1 + ∑ b, finiteMean (fun a => f a b) := finiteMean_one_add_sum f
    _ ≤ 1 + ∑ _b : β, B := add_le_add_right (Finset.sum_le_sum (fun b _ => hf b)) 1
    _ = 1 + Fintype.card β * B := by simp

end VertexCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
