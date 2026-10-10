import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumClockStep

namespace OAI

/-! The valid clock sector is exactly the finite circuit clock, with its
full complement retained in the norm decomposition. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaHistoryClockEquiv (T : ℕ) :
    Fin (T+1) ≃ {s : SourceSpinBasis (T+2) // QMALegalClock T s} :=
  Equiv.ofBijective (fun t => ⟨qmaHistoryClock T t,qmaHistoryClock_legal T t⟩) (by
    constructor
    · intro s t h
      exact qmaHistoryClock_injective T (congrArg Subtype.val h)
    · intro s
      obtain ⟨t,ht⟩ := qmaHistoryClock_of_legal T s.val s.property
      exact ⟨t,Subtype.ext ht⟩)

theorem qmaClock_sector_sum (T : ℕ) (f : SourceSpinBasis (T+2) → ℝ) :
    (∑ s, f s) = (∑ t : Fin (T+1), f (qmaHistoryClock T t))+
      ∑ s, if QMALegalClock T s then 0 else f s := by
  have he := (qmaHistoryClockEquiv T).sum_comp (fun s => f s.val)
  have hs := Finset.sum_subtype (F := inferInstance)
    (Finset.univ.filter (QMALegalClock T))
    (by simp : ∀ s, s ∈ Finset.univ.filter (QMALegalClock T) ↔ QMALegalClock T s) f
  rw [Finset.sum_filter] at hs
  have hsplit : (∑ s, f s) =
      (∑ s, if QMALegalClock T s then f s else 0)+
      ∑ s, if QMALegalClock T s then 0 else f s := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : QMALegalClock T s <;> simp [h]
  rw [hsplit,hs,←he]
  rfl

theorem qmaClock_invalid_mass_bound (T : ℕ) (f : SourceSpinBasis (T+2) → ℝ)
    (hf : ∀ s, 0 ≤ f s) :
    (∑ s, if QMALegalClock T s then 0 else f s) ≤
      ∑ s, qmaPinnedClockPenalty T s*f s := by
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : QMALegalClock T s
  · simp only [ite_eq_left hs]
    exact mul_nonneg (qmaPinnedClockPenalty_nonneg T s) (hf s)
  · simp only [ite_eq_right hs]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (qmaPinnedClockPenalty_one_le T s hs) (hf s)

end ContinuumCoulomb

end

end OAI
