import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTermTime

namespace OAI

/-! Coverage at every clock time bounds jumps in the ordered interaction list. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

variable {α : Type*}

theorem qmaSortedTime_step {T : ℕ} (time : α → Fin T) (xs : List α)
    (hs : xs.Pairwise (fun a b => time a ≤ time b))
    (hc : ∀ t : Fin T, ∃ a ∈ xs, time a = t)
    (i j : Fin xs.length) (hj : j.val = i.val+1) :
    (time xs[j.val]).val ≤ (time xs[i.val]).val+1 := by
  by_contra hn
  have hgap : (time xs[i.val]).val+1 < (time xs[j.val]).val := by omega
  let t : Fin T := ⟨(time xs[i.val]).val+1,lt_trans hgap (time xs[j.val]).isLt⟩
  obtain ⟨a,ha,hat⟩ := hc t
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp ha
  have hk' : xs[k.val] = a := hk
  by_cases hki : k.val ≤ i.val
  · have hle : time xs[k.val] ≤ time xs[i.val] := by
      rcases lt_or_eq_of_le hki with hl | he
      · exact hs.rel_getElem_of_lt k.isLt i.isLt hl
      · simp only [he,le_refl]
    rw [hk',hat] at hle
    change (time xs[i.val]).val+1 ≤ (time xs[i.val]).val at hle
    omega
  · have hjk : j.val ≤ k.val := by omega
    have hle : time xs[j.val] ≤ time xs[k.val] := by
      rcases lt_or_eq_of_le hjk with hl | he
      · exact hs.rel_getElem_of_lt j.isLt k.isLt hl
      · simp only [he,le_refl]
    rw [hk',hat] at hle
    change (time xs[j.val]).val ≤ (time xs[i.val]).val+1 at hle
    omega

theorem qmaOrderedHistoryTerms_cover (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (t : Fin c.gates.length) :
    ∃ a ∈ qmaOrderedHistoryTerms c hT τ, qmaHistoryTermTime c hT τ a = t := by
  refine ⟨.inr (.inr (.inr (.inr t))),qmaOrderedHistoryTerms_mem c hT τ _,rfl⟩

theorem qmaOrderedHistoryTerms_step (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (i j : Fin (qmaOrderedHistoryTerms c hT τ).length) (hj : j.val = i.val+1) :
    (qmaHistoryTermTime c hT τ (qmaOrderedHistoryTerms c hT τ)[j.val]).val ≤
      (qmaHistoryTermTime c hT τ (qmaOrderedHistoryTerms c hT τ)[i.val]).val+1 :=
  qmaSortedTime_step _ _ (qmaOrderedHistoryTerms_sorted c hT τ)
    (qmaOrderedHistoryTerms_cover c hT τ) i j hj

end ContinuumCoulomb

end

end OAI
