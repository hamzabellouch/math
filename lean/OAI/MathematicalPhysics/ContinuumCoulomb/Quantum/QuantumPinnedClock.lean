import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnaryPenalty

namespace OAI

/-! Two fixed end bits make all clock transitions uniform, including the
empty circuit. Only adjacent-pair and endpoint penalties are used. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaHistoryClock (T : ℕ) (t : Fin (T+1)) : SourceSpinBasis (T+2) :=
  qmaUnaryClock (T+2) ⟨t.val+1,by omega⟩

def QMALegalClock (T : ℕ) (s : SourceSpinBasis (T+2)) : Prop :=
  Antitone s ∧ s 0 = 1 ∧ s (Fin.last (T+1)) = 0

theorem qmaHistoryClock_injective (T : ℕ) : Function.Injective (qmaHistoryClock T) := by
  intro s t h
  have he := qmaUnaryClock_injective (T+2) h
  apply Fin.ext
  have hv := congrArg Fin.val he
  simpa using hv

theorem qmaHistoryClock_legal (T : ℕ) (t : Fin (T+1)) :
    QMALegalClock T (qmaHistoryClock T t) := by
  refine ⟨qmaUnaryClock_antitone _ _,?_,?_⟩
  · simp [qmaHistoryClock,qmaUnaryClock]
  · have ht : ¬T+1 < t.val+1 := by omega
    simpa [qmaHistoryClock,qmaUnaryClock] using ht

theorem qmaHistoryClock_of_legal (T : ℕ) (s : SourceSpinBasis (T+2))
    (hs : QMALegalClock T s) : ∃ t : Fin (T+1), qmaHistoryClock T t = s := by
  obtain ⟨k,hk⟩ := qmaUnaryClock_of_antitone (T+2) s hs.1
  have hl := hs.2.1
  have hr := hs.2.2
  rw [←hk] at hl hr
  have hk0 : 0 < k.val := by
    by_contra hn
    have hz : k.val = 0 := by omega
    simp [qmaUnaryClock,hz] at hl
  have hk1 : k.val ≤ T+1 := by
    by_contra hn
    have ht : T+1 < k.val := by omega
    simp [qmaUnaryClock,ht] at hr
  refine ⟨⟨k.val-1,by omega⟩,?_⟩
  unfold qmaHistoryClock
  have he : (⟨k.val-1+1,by omega⟩ : Fin (T+2+1)) = k := by
    apply Fin.ext
    change k.val-1+1 = k.val
    omega
  rw [he]
  exact hk

def qmaPinnedClockPenalty (T : ℕ) (s : SourceSpinBasis (T+2)) : ℝ :=
  qmaClockFaultCount (T+2) s+
    (if s 0 = 1 then 0 else 1)+(if s (Fin.last (T+1)) = 0 then 0 else 1)

theorem qmaPinnedClockPenalty_nonneg (T : ℕ) (s : SourceSpinBasis (T+2)) :
    0 ≤ qmaPinnedClockPenalty T s := by
  unfold qmaPinnedClockPenalty
  have h := qmaClockFaultCount_nonneg (T+2) s
  positivity

theorem qmaPinnedClockPenalty_zero (T : ℕ) (s : SourceSpinBasis (T+2))
    (hs : QMALegalClock T s) : qmaPinnedClockPenalty T s = 0 := by
  simp [qmaPinnedClockPenalty,qmaClockFaultCount_zero _ _ hs.1,hs.2.1,hs.2.2]

theorem qmaPinnedClockPenalty_one_le (T : ℕ) (s : SourceSpinBasis (T+2))
    (hs : ¬QMALegalClock T s) : 1 ≤ qmaPinnedClockPenalty T s := by
  have hn := qmaClockFaultCount_nonneg (T+2) s
  by_cases ha : Antitone s
  · by_cases hl : s 0 = 1
    · have hr : s (Fin.last (T+1)) ≠ 0 := fun h => hs ⟨ha,hl,h⟩
      simp only [qmaPinnedClockPenalty,ite_eq_left hl,ite_eq_right hr,add_zero]
      linarith
    · unfold qmaPinnedClockPenalty
      rw [ite_eq_right hl]
      split <;> linarith
  · have h := qmaClockFaultCount_one_le (T+2) s ha
    unfold qmaPinnedClockPenalty
    split <;> split <;> linarith

end ContinuumCoulomb

end

end OAI
