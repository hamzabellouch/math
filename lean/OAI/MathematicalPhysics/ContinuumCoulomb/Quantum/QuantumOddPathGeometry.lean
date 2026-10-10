import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridWalk

namespace OAI

/-! The odd subdivision gadget splits a routed edge into two unit edges and
its reversed remaining tail. The two fresh vertices are the first two route points. -/

namespace ContinuumCoulomb

def qmaOddSplitLength (L : ℕ) : Fin 3 → ℕ := ![1,1,L-2]
def qmaOddSplitIndex (L : ℕ) (e : Fin 3) (k : ℕ) : ℕ :=
  if e = 0 then k+1 else if e = 1 then k else L-k

theorem qmaOddSplitIndex_bounds {L : ℕ} (hL : 3 ≤ L) (e : Fin 3) {k : ℕ}
    (hk : k ≤ qmaOddSplitLength L e) : qmaOddSplitIndex L e k ≤ L := by
  fin_cases e <;> simp [qmaOddSplitLength,qmaOddSplitIndex] at * <;> omega

theorem qmaOddSplitIndex_zero (L : ℕ) :
    (fun e => qmaOddSplitIndex L e 0) = ![1,0,L] := by
  funext e
  fin_cases e <;> simp [qmaOddSplitIndex]

theorem qmaOddSplitIndex_last {L : ℕ} (hL : 3 ≤ L) :
    (fun e => qmaOddSplitIndex L e (qmaOddSplitLength L e)) = ![2,1,2] := by
  funext e
  fin_cases e <;> simp [qmaOddSplitLength,qmaOddSplitIndex]
  omega

theorem qmaOddSplitIndex_injective {L : ℕ} (hL : 3 ≤ L) (e : Fin 3)
    {i j : ℕ} (hi : i ≤ qmaOddSplitLength L e) (hj : j ≤ qmaOddSplitLength L e)
    (h : qmaOddSplitIndex L e i = qmaOddSplitIndex L e j) : i = j := by
  fin_cases e <;> (simp [qmaOddSplitLength,qmaOddSplitIndex] at *; omega)

theorem qmaOddSplitIndex_interior {L : ℕ} (hL : 3 ≤ L) (e : Fin 3) {i : ℕ}
    (hi0 : 0 < i) (hi : i < qmaOddSplitLength L e) :
    e = 2 ∧ 2 < qmaOddSplitIndex L e i ∧ qmaOddSplitIndex L e i < L := by
  fin_cases e <;> simp [qmaOddSplitLength,qmaOddSplitIndex] at * <;> omega

theorem qmaOddSplitIndex_separated {L : ℕ} (hL : 3 ≤ L) (e f : Fin 3) {i j : ℕ}
    (hi0 : 0 < i) (hi : i < qmaOddSplitLength L e)
    (hj : j ≤ qmaOddSplitLength L f)
    (h : qmaOddSplitIndex L e i = qmaOddSplitIndex L f j) : e = f := by
  obtain ⟨rfl,hi2,hiL⟩ := qmaOddSplitIndex_interior hL e hi0 hi
  fin_cases f <;> simp [qmaOddSplitLength,qmaOddSplitIndex] at * <;> omega

theorem qmaOddSplitIndex_step {L : ℕ} (hL : 3 ≤ L) (e : Fin 3) {i : ℕ}
    (hi : i < qmaOddSplitLength L e) :
    qmaOddSplitIndex L e (i+1) = qmaOddSplitIndex L e i+1 ∨
      qmaOddSplitIndex L e i = qmaOddSplitIndex L e (i+1)+1 := by
  fin_cases e <;> simp [qmaOddSplitLength,qmaOddSplitIndex] at *
  omega

theorem qmaOddSplitPoint_step {L : ℕ} (hL : 3 ≤ L) (p : ℕ → ℕ × ℕ)
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1))) (e : Fin 3) {i : ℕ}
    (hi : i < qmaOddSplitLength L e) :
    qmaSquareGrid.Adj (p (qmaOddSplitIndex L e i)) (p (qmaOddSplitIndex L e (i+1))) := by
  rcases qmaOddSplitIndex_step hL e hi with h | h
  · have hn := qmaOddSplitIndex_bounds hL e (k := i+1) (Nat.succ_le_iff.mpr hi)
    have hk : qmaOddSplitIndex L e i < L := by omega
    simpa only [h] using hp (qmaOddSplitIndex L e i) hk
  · have hb := qmaOddSplitIndex_bounds hL e (k := i) (Nat.le_of_lt hi)
    have hk : qmaOddSplitIndex L e (i+1) < L := by omega
    simpa only [h] using (hp (qmaOddSplitIndex L e (i+1)) hk).symm

end ContinuumCoulomb

end OAI
