import OAI.NumberTheory.Ostmann.Arithmetic.MovingRestoredPrimeLaws

namespace OAI

/-! # Restoration preserves the terminal-tier separation -/

namespace Ostmann
open scoped Classical

@[simp] theorem movingRestoredTiers_compensation (n r m : ℕ)
    (tier : MovingRegularSlot n r m → ℕ) (i : TreeLeafIndex n × Fin 4) :
    movingRestoredTiers n r m tier (movingReverseTemplate n r m (.inl i)) = n := by
  simp only [movingRestoredTiers, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem movingRestoredTiers_surviving (n r m : ℕ)
    (tier : MovingRegularSlot n r m → ℕ) (i : MovingRegularSlot n r m) :
    movingRestoredTiers n r m tier (movingReverseTemplate n r m (.inr i)) = tier i := by
  simp only [movingRestoredTiers, Equiv.symm_apply_apply, Sum.elim_inr]

theorem movingRestoredTiers_small (n r m k : ℕ) (hn : n ≠ k)
    (tier : MovingRegularSlot n r m → ℕ)
    (h : ∀ j : TreeLeafIndex n × Fin r, tier (j.1, .inl j.2) ≠ k) :
    ∀ j : TreeLeafIndex n × Fin (4 + r),
      movingRestoredTiers n r m tier (j.1, .inl j.2) ≠ k := by
  rintro ⟨j, i⟩
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · change movingRestoredTiers n r m tier
      (movingReverseTemplate n r m (.inl (j, a))) ≠ k
    simpa only [movingRestoredTiers_compensation] using hn
  · change movingRestoredTiers n r m tier
      (movingReverseTemplate n r m (.inr (j, .inl b))) ≠ k
    simpa only [movingRestoredTiers_surviving] using h (j, b)

theorem movingRestoredTiers_bulk (n r m k : ℕ)
    (tier : MovingRegularSlot n r m → ℕ)
    (h : ∀ j, tier (movingTemplateBulk n r m j) = k) :
    ∀ j, movingRestoredTiers n r m tier (movingTemplateBulk n (4 + r) m j) = k := by
  intro j
  rw [← movingReverseTemplate_bulk, movingRestoredTiers_surviving]
  exact h j

end Ostmann

end OAI
