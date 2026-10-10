import OAI.Analysis.LipschitzHilbert.Packets.ShortPacketBoxes

namespace OAI

/-! Exact center-box grouping for finite positive sums. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem short_sum_eq_boxes {σ : Type*} {ι : σ → Type*} [Fintype σ] [∀ j, Fintype (ι j)]
    (len : σ → ℝ) (index : ∀ j, ι j → ℤ × ℤ) (r : ℝ)
    (a : ∀ j, ι j → ℝ) (j : σ) :
    (if len j ≤ r then ∑ i, a j i else 0) =
      ∑ b ∈ allPacketBoxes index, ∑ i : ShortBoxFiber len index r b j, a j i := by
  have hf (b : ℤ × ℤ) : (∑ i : ShortBoxFiber len index r b j, a j i) =
      ∑ i : ι j, if len j ≤ r ∧ index j i = b then a j i else 0 := by
    have h := Finset.sum_subtype (Finset.univ.filter (fun i : ι j => len j ≤ r ∧ index j i = b))
      (p := fun i : ι j => len j ≤ r ∧ index j i = b) (F := inferInstance)
      (by simp) (a j)
    simpa only [Finset.sum_filter] using h.symm
  simp_rw [hf]
  rw [Finset.sum_comm]
  by_cases hj : len j ≤ r
  · simp only [hj, true_and, ite_true]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single (index j i)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hi
      exact (hi (mem_allPacketBoxes index j i)).elim
  · simp [hj]

end LipschitzHilbert

end

end OAI
