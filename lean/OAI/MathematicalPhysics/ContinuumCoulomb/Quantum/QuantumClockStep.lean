import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumClockTransition

namespace OAI

/-! Each active guarded clock pair is either entirely legal or entirely
illegal; its legal pair is the intended consecutive history pair. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaClock_step_guard (T : ℕ) (i : Fin T) :
    QMAClockGuard T i (qmaHistoryClock T i.castSucc) := by
  constructor
  · simp [qmaHistoryClock,qmaUnaryClock,qmaClockLeft]
  · simp [qmaHistoryClock,qmaUnaryClock,qmaClockRight]

theorem qmaClock_step_zero (T : ℕ) (i : Fin T) :
    qmaHistoryClock T i.castSucc (qmaClockMiddle T i) = 0 := by
  simp [qmaHistoryClock,qmaUnaryClock,qmaClockMiddle]

theorem qmaClock_step_update (T : ℕ) (i : Fin T) :
    Function.update (qmaHistoryClock T i.castSucc) (qmaClockMiddle T i) 1 =
      qmaHistoryClock T i.succ := by
  funext j
  by_cases hj : j = qmaClockMiddle T i
  · subst j
    simp [qmaHistoryClock,qmaUnaryClock,qmaClockMiddle]
  · rw [Function.update_of_ne hj]
    have hn : j.val ≠ i.val+1 := fun h => hj (Fin.ext h)
    have he : j.val < i.val+1 ↔ j.val < i.val+1+1 := by omega
    simp only [qmaHistoryClock,qmaUnaryClock,Fin.val_castSucc,Fin.val_succ,he]

theorem qmaClock_step_legal_iff (T : ℕ) (i : Fin T) (s : SourceSpinBasis (T+2))
    (hg : QMAClockGuard T i s) (hz : s (qmaClockMiddle T i) = 0) :
    QMALegalClock T (Function.update s (qmaClockMiddle T i) 1) ↔ QMALegalClock T s := by
  constructor
  · intro hs
    have hg' : QMAClockGuard T i (Function.update s (qmaClockMiddle T i) 1) :=
      (qmaClockGuard_update T i s 1).mpr hg
    have h := qmaClock_update_legal T i _ hs hg' 0
    rw [Function.update_idem,←hz,Function.update_eq_self] at h
    exact h
  · intro hs
    exact qmaClock_update_legal T i s hs hg 1

theorem qmaClock_step_legal_before (T : ℕ) (i : Fin T) (s : SourceSpinBasis (T+2))
    (hg : QMAClockGuard T i s) (hz : s (qmaClockMiddle T i) = 0)
    (hs : QMALegalClock T s) : qmaHistoryClock T i.castSucc = s := by
  obtain ⟨t,ht⟩ := qmaHistoryClock_of_legal T s hs
  have hl : i.val < t.val+1 := by
    by_contra hn
    have h := hg.1
    rw [←ht] at h
    simp [qmaHistoryClock,qmaUnaryClock,qmaClockLeft,hn] at h
  have hm : ¬i.val+1 < t.val+1 := by
    intro hn
    rw [←ht] at hz
    simp [qmaHistoryClock,qmaUnaryClock,qmaClockMiddle,hn] at hz
  have he : t = i.castSucc := by
    apply Fin.ext
    simp only [Fin.val_castSucc]
    omega
  simpa only [he] using ht

end ContinuumCoulomb

end

end OAI
