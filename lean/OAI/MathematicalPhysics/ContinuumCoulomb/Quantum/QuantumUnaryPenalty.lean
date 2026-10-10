import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnaryClock

namespace OAI

/-! The adjacent 01 penalties separate all invalid unary clock states. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaClockFaultCount : (N : ℕ) → SourceSpinBasis N → ℝ
  | 0, _ => 0
  | n+1, s => ∑ i : Fin n, if s i.castSucc = 0 ∧ s i.succ = 1 then 1 else 0

theorem qmaClockFaultCount_nonneg (N : ℕ) (s : SourceSpinBasis N) :
    0 ≤ qmaClockFaultCount N s := by
  cases N with
  | zero => rfl
  | succ n => unfold qmaClockFaultCount; positivity

theorem qmaClockFaultCount_zero (N : ℕ) (s : SourceSpinBasis N) (hs : Antitone s) :
    qmaClockFaultCount N s = 0 := by
  cases N with
  | zero => rfl
  | succ n =>
    apply Finset.sum_eq_zero
    intro i _
    have hi := hs (Fin.castSucc_lt_succ (i := i)).le
    have hn : ¬(s i.castSucc = 0 ∧ s i.succ = 1) := by
      rintro ⟨hl,hr⟩
      rw [hl,hr] at hi
      norm_num at hi
    simp [hn]

theorem qmaClockFaultCount_one_le (N : ℕ) (s : SourceSpinBasis N) (hs : ¬Antitone s) :
    1 ≤ qmaClockFaultCount N s := by
  cases N with
  | zero =>
    exfalso
    apply hs
    intro i
    exact Fin.elim0 i
  | succ n =>
    have hn : ¬∀ i : Fin n, s i.succ ≤ s i.castSucc :=
      fun h => hs (Fin.antitone_iff_succ_le.mpr h)
    obtain ⟨i,hi⟩ := not_forall.mp hn
    have hv : s i.castSucc = 0 ∧ s i.succ = 1 := by
      constructor <;> apply Fin.ext
      all_goals
        have hleft := (s i.castSucc).isLt
        have hright := (s i.succ).isLt
        simp only [Fin.le_def] at hi
        simp only [Fin.val_zero,Fin.val_one]
        omega
    have h := Finset.single_le_sum
      (f := fun j : Fin n => if s j.castSucc = 0 ∧ s j.succ = 1 then (1:ℝ) else 0)
      (s := Finset.univ) (a := i) (by intro j _; positivity) (Finset.mem_univ _)
    simpa only [qmaClockFaultCount,ite_eq_left hv] using h

theorem qmaClockFaultCount_unary (N : ℕ) (t : Fin (N+1)) :
    qmaClockFaultCount N (qmaUnaryClock N t) = 0 :=
  qmaClockFaultCount_zero N _ (qmaUnaryClock_antitone N t)

theorem qmaClockFaultCount_invalid (N : ℕ) (s : SourceSpinBasis N)
    (hs : ¬∃ t : Fin (N+1), qmaUnaryClock N t = s) :
    1 ≤ qmaClockFaultCount N s :=
  qmaClockFaultCount_one_le N s (fun h => hs (qmaUnaryClock_of_antitone N s h))

end ContinuumCoulomb

end

end OAI
