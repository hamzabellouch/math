import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathSchedule
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOddPathGeometry

namespace OAI

/-! Each edge of an odd-subdivision round is an explicitly indexed piece of
one previous route. Interior points of distinct pieces cannot coincide. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPathSchedule

def nextParent (W : QMAPathSchedule) : QMAPartialPathsEdge W.active → W.graph.Edge
  | .inl e => e.val
  | .inr (.inl i) => qmaSelectedIndex W.active i
  | .inr (.inr (i,_)) => qmaSelectedIndex W.active i

def nextIndex (W : QMAPathSchedule) (e : QMAPartialPathsEdge W.active) (k : ℕ) : ℕ :=
  match e with
  | .inl _ => k
  | .inr (.inl _) => k+1
  | .inr (.inr (i,a)) => if a = 0 then k else 2*W.work (qmaSelectedIndex W.active i)+1-k

theorem retained_work_zero (W : QMAPathSchedule) (e : {e // e ∉ W.active}) :
    W.work e.val = 0 := by
  have h := e.property
  simp only [mem_active] at h
  omega

theorem selected_work_pos (W : QMAPathSchedule) (i : Fin W.active.card) :
    0 < W.work (qmaSelectedIndex W.active i) :=
  (W.mem_active _).mp (qmaSelectedIndex_mem W.active i)

theorem nextIndex_bounds (W : QMAPathSchedule) (e : QMAPartialPathsEdge W.active) {k : ℕ}
    (hk : k ≤ 2*W.nextWork e+1) : W.nextIndex e k ≤ 2*W.work (W.nextParent e)+1 := by
  rcases e with e | (i | ⟨i,a⟩)
  · simpa only [nextIndex,nextParent,nextWork,W.retained_work_zero e,Nat.mul_zero,
      Nat.zero_add] using hk
  · have hp := W.selected_work_pos i
    simp only [nextIndex,nextParent,nextWork,Nat.mul_zero,Nat.zero_add] at *
    omega
  · have hp := W.selected_work_pos i
    fin_cases a <;> simp [nextIndex,nextParent,nextWork] at *
    omega

theorem nextIndex_injective (W : QMAPathSchedule) (e : QMAPartialPathsEdge W.active) {i j : ℕ}
    (hi : i ≤ 2*W.nextWork e+1) (hj : j ≤ 2*W.nextWork e+1)
    (h : W.nextIndex e i = W.nextIndex e j) : i = j := by
  rcases e with e | (a | ⟨a,b⟩)
  · exact h
  · simpa only [nextIndex,Nat.add_right_cancel_iff] using h
  · have hp := W.selected_work_pos a
    fin_cases b <;> simp [nextIndex,nextWork] at * <;> omega

theorem nextIndex_interior (W : QMAPathSchedule) (e : QMAPartialPathsEdge W.active) {i : ℕ}
    (hi0 : 0 < i) (hi : i < 2*W.nextWork e+1) :
    2 < W.nextIndex e i ∧ W.nextIndex e i < 2*W.work (W.nextParent e)+1 := by
  rcases e with e | (a | ⟨a,b⟩)
  · simp only [nextWork,Nat.mul_zero,Nat.zero_add] at hi
    omega
  · simp only [nextWork,Nat.mul_zero,Nat.zero_add] at hi
    omega
  · have hp := W.selected_work_pos a
    fin_cases b <;> simp [nextIndex,nextParent,nextWork] at * <;> omega

theorem nextIndex_step (W : QMAPathSchedule) (e : QMAPartialPathsEdge W.active) {i : ℕ}
    (hi : i < 2*W.nextWork e+1) :
    W.nextIndex e (i+1) = W.nextIndex e i+1 ∨
      W.nextIndex e i = W.nextIndex e (i+1)+1 := by
  rcases e with e | (a | ⟨a,b⟩)
  · exact Or.inl rfl
  · exact Or.inl rfl
  · have hp := W.selected_work_pos a
    fin_cases b <;> simp [nextIndex,nextWork] at *
    omega

theorem selectedIndex_injective (W : QMAPathSchedule) :
    Function.Injective (qmaSelectedIndex W.active) := by
  intro i j h
  apply W.active.equivFin.symm.injective
  exact Subtype.ext h

theorem nextIndex_separated (W : QMAPathSchedule) (e f : QMAPartialPathsEdge W.active)
    {i j : ℕ} (hi0 : 0 < i) (hi : i < 2*W.nextWork e+1)
    (hj : j ≤ 2*W.nextWork f+1) (he : W.nextParent e = W.nextParent f)
    (hp : W.nextIndex e i = W.nextIndex f j) : e = f := by
  have hinner := W.nextIndex_interior e hi0 hi
  rcases e with e | (a | ⟨a,b⟩)
  · simp only [nextWork,Nat.mul_zero,Nat.zero_add] at hi
    omega
  · simp only [nextWork,Nat.mul_zero,Nat.zero_add] at hi
    omega
  · fin_cases b
    · simp [nextWork] at hi
      omega
    rcases f with f | (c | ⟨c,d⟩)
    · have hret := W.retained_work_zero f
      have hpos := W.selected_work_pos a
      change qmaSelectedIndex W.active a = f.val at he
      rw [he,hret] at hpos
      omega
    · change qmaSelectedIndex W.active a = qmaSelectedIndex W.active c at he
      have hac := W.selectedIndex_injective he
      subst c
      simp [nextIndex,nextWork] at hj hp
      simp [nextIndex] at hinner
      omega
    · change qmaSelectedIndex W.active a = qmaSelectedIndex W.active c at he
      have hac := W.selectedIndex_injective he
      subst c
      fin_cases d
      · simp [nextIndex,nextWork] at hj hp
        simp [nextIndex] at hinner
        omega
      · rfl

end QMAPathSchedule
end ContinuumCoulomb

end

end OAI
