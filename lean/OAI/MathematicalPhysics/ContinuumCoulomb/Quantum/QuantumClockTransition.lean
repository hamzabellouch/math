import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPinnedClock

namespace OAI

/-! A guarded single-bit clock update preserves the legal clock sector.
The guard inspects only the two adjacent clock bits. -/

noncomputable section
namespace ContinuumCoulomb

def qmaClockLeft (T : ℕ) (i : Fin T) : Fin (T+2) := ⟨i.val,by omega⟩
def qmaClockMiddle (T : ℕ) (i : Fin T) : Fin (T+2) := ⟨i.val+1,by omega⟩
def qmaClockRight (T : ℕ) (i : Fin T) : Fin (T+2) := ⟨i.val+2,by omega⟩

def QMAClockGuard (T : ℕ) (i : Fin T) (s : SourceSpinBasis (T+2)) : Prop :=
  s (qmaClockLeft T i) = 1 ∧ s (qmaClockRight T i) = 0

theorem qmaClockLeft_ne_middle (T : ℕ) (i : Fin T) :
    qmaClockLeft T i ≠ qmaClockMiddle T i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [qmaClockLeft,qmaClockMiddle] at hv
  omega

theorem qmaClockRight_ne_middle (T : ℕ) (i : Fin T) :
    qmaClockRight T i ≠ qmaClockMiddle T i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [qmaClockRight,qmaClockMiddle] at hv
  omega

theorem qmaClockGuard_update (T : ℕ) (i : Fin T) (s : SourceSpinBasis (T+2)) (a : Fin 2) :
    QMAClockGuard T i (Function.update s (qmaClockMiddle T i) a) ↔ QMAClockGuard T i s := by
  simp only [QMAClockGuard,Function.update_of_ne (qmaClockLeft_ne_middle T i),
    Function.update_of_ne (qmaClockRight_ne_middle T i)]

theorem qmaClock_update_antitone (T : ℕ) (i : Fin T) (s : SourceSpinBasis (T+2))
    (hs : Antitone s) (hg : QMAClockGuard T i s) (a : Fin 2) :
    Antitone (Function.update s (qmaClockMiddle T i) a) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro j
  by_cases hl : j.castSucc = qmaClockMiddle T i
  · have hr : j.succ = qmaClockRight T i := by
      apply Fin.ext
      have hv := congrArg Fin.val hl
      dsimp [qmaClockMiddle] at hv
      change j.val+1 = i.val+2
      omega
    rw [hl,hr,Function.update_self,Function.update_of_ne (qmaClockRight_ne_middle T i),hg.2]
    exact Fin.zero_le a
  · by_cases hr : j.succ = qmaClockMiddle T i
    · have hleft : j.castSucc = qmaClockLeft T i := by
        apply Fin.ext
        have hv := congrArg Fin.val hr
        dsimp [qmaClockMiddle] at hv
        change j.val = i.val
        omega
      rw [hr,hleft,Function.update_self,Function.update_of_ne (qmaClockLeft_ne_middle T i),hg.1]
      change a.val ≤ 1
      have ha := a.isLt
      omega
    · rw [Function.update_of_ne hl,Function.update_of_ne hr]
      exact hs (Fin.castSucc_lt_succ (i := j)).le

theorem qmaClock_update_legal (T : ℕ) (i : Fin T) (s : SourceSpinBasis (T+2))
    (hs : QMALegalClock T s) (hg : QMAClockGuard T i s) (a : Fin 2) :
    QMALegalClock T (Function.update s (qmaClockMiddle T i) a) := by
  refine ⟨qmaClock_update_antitone T i s hs.1 hg a,?_,?_⟩
  · have hn : (0 : Fin (T+2)) ≠ qmaClockMiddle T i := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [qmaClockMiddle] at hv
      omega
    rw [Function.update_of_ne hn]
    exact hs.2.1
  · have hn : Fin.last (T+1) ≠ qmaClockMiddle T i := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [qmaClockMiddle] at hv
      have hi := i.isLt
      omega
    rw [Function.update_of_ne hn]
    exact hs.2.2

end ContinuumCoulomb

end

end OAI
