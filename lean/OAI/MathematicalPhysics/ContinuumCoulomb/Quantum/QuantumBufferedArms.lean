import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedDetour
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridWalk

namespace OAI

/-! Uniform finite-walk interface for all three buffered endpoint arms. -/

namespace ContinuumCoulomb

def qmaBufferedArmLength (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) : ℕ :=
  if a = 2 then qmaBufferedPort c a + qmaBufferedOffset c side a + 1
  else qmaBufferedDoglegLength (qmaBufferedPort c a) (qmaBufferedOffset c side a)

def qmaBufferedArmPoint (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) (k : ℕ) : ℕ × ℕ :=
  if a = 0 then qmaBufferedDoglegPoint (qmaBufferedPort c a) (qmaBufferedOffset c side a) k
  else if a = 1 then (qmaBufferedDoglegPoint (qmaBufferedPort c a) (qmaBufferedOffset c side a) k).swap
  else qmaBufferedDetourPoint (qmaBufferedPort c a) (qmaBufferedOffset c side a) k

theorem qmaBufferedOffset_ne (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) :
    qmaBufferedPort c a ≠ qmaBufferedOffset c side a := by
  unfold qmaBufferedOffset qmaBufferedPort
  split_ifs <;> omega

@[simp] theorem qmaBufferedArm_zero (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) :
    qmaBufferedArmPoint c side a 0 = (17,17) := by
  fin_cases a <;> simp [qmaBufferedArmPoint,qmaBufferedDogleg_zero,qmaBufferedDetour_zero]

@[simp] theorem qmaBufferedArm_last (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) :
    qmaBufferedArmPoint c side a (qmaBufferedArmLength c side a) =
      (qmaBufferedPort c a,qmaBufferedPort c a) := by
  have hu : 24 ≤ qmaBufferedPort c 2 := by unfold qmaBufferedPort; omega
  fin_cases a <;> simp [qmaBufferedArmPoint,qmaBufferedArmLength,
    qmaBufferedDogleg_last,qmaBufferedDetour_last hu]

theorem qmaBufferedArm_support (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3) (k : ℕ) :
    qmaBufferedFanoutSupport c side a (qmaBufferedArmPoint c side a k) := by
  have hu : 24 ≤ qmaBufferedPort c 1 := by unfold qmaBufferedPort; omega
  have hv : 23 ≤ qmaBufferedOffset c side 1 := by
    have h := qmaBufferedOffset_bounds c side 1
    omega
  fin_cases a
  · exact qmaBufferedFanout_direct_support c side k
  · have h := qmaBufferedDogleg_support hu hv k
    simpa [qmaBufferedFanoutSupport,qmaBufferedDoglegSupport,qmaBufferedArmPoint] using h
  · exact qmaBufferedFanout_detour_support c side k

theorem qmaBufferedArm_step (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (a : Fin 3)
    (k : ℕ) (hk : k < qmaBufferedArmLength c side a) :
    qmaSquareGrid.Adj (qmaBufferedArmPoint c side a k) (qmaBufferedArmPoint c side a (k+1)) := by
  have hu : 24 ≤ qmaBufferedPort c a := by unfold qmaBufferedPort; omega
  have hc := qmaBufferedOffset_bounds c side a
  have hv : 23 ≤ qmaBufferedOffset c side a := by omega
  have hn := qmaBufferedOffset_ne c side a
  fin_cases a
  · simpa [qmaBufferedArmPoint,qmaSquareGrid] using
      qmaBufferedDogleg_step hu hv hc hn k hk
  · simpa [qmaBufferedArmPoint,qmaSquareGrid,Nat.add_comm] using
      qmaBufferedDogleg_step hu hv hc hn k hk
  · simpa [qmaBufferedArmPoint,qmaSquareGrid] using
      qmaBufferedDetour_step hu hv hc hn k hk

theorem qmaBufferedArm_length_bound (c : Fin 3 → ℕ) (side : Fin 3 → Bool)
    {C : ℕ} (hC : ∀ a, c a < C) (a : Fin 3) : qmaBufferedArmLength c side a ≤ 16*(C+3)+2 := by
  have hu : qmaBufferedPort c a ≤ 8*(C+3) := by
    have h := hC a
    unfold qmaBufferedPort
    omega
  have hc := qmaBufferedOffset_bounds c side a
  unfold qmaBufferedArmLength
  split_ifs
  · omega
  · exact (qmaBufferedDogleg_length_bound hu hc.2).trans (by omega)

end ContinuumCoulomb

end OAI
