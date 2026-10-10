import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedFanout

namespace OAI

/-! The two direct buffered endpoint arms, including their one-step joins. -/

namespace ContinuumCoulomb

def qmaBufferedDoglegLength (u v : ℕ) : ℕ := (v-17)+(u-17)+1

def qmaBufferedDoglegPoint (u v k : ℕ) : ℕ × ℕ :=
  if k ≤ v-17 then (17+k,17)
  else if k ≤ (v-17)+(u-17) then (v,17+(k-(v-17)))
  else (u,u)

def qmaBufferedDoglegSupport (u v : ℕ) (p : ℕ × ℕ) : Prop :=
  (p.2 = 17 ∧ 17 ≤ p.1 ∧ p.1 ≤ v) ∨
  (p.1 = v ∧ 17 ≤ p.2 ∧ p.2 ≤ u) ∨
  (p.2 = u ∧ qmaBetween v u p.1)

theorem qmaBufferedDogleg_zero (u v : ℕ) : qmaBufferedDoglegPoint u v 0 = (17,17) := by
  simp [qmaBufferedDoglegPoint]

theorem qmaBufferedDogleg_last (u v : ℕ) :
    qmaBufferedDoglegPoint u v (qmaBufferedDoglegLength u v) = (u,u) := by
  unfold qmaBufferedDoglegPoint qmaBufferedDoglegLength
  rw [ite_eq_right (by omega),ite_eq_right (by omega)]

theorem qmaBufferedDogleg_support {u v : ℕ} (hu : 24 ≤ u) (hv : 23 ≤ v) (k : ℕ) :
    qmaBufferedDoglegSupport u v (qmaBufferedDoglegPoint u v k) := by
  unfold qmaBufferedDoglegPoint
  split_ifs <;> simp [qmaBufferedDoglegSupport,qmaBetween] <;> omega

theorem qmaBufferedDogleg_step {u v : ℕ} (hu : 24 ≤ u) (hv : 23 ≤ v)
    (hclose : u ≤ v+1 ∧ v ≤ u+1) (hne : u ≠ v) (k : ℕ)
    (hk : k < qmaBufferedDoglegLength u v) :
    Nat.dist (qmaBufferedDoglegPoint u v k).1 (qmaBufferedDoglegPoint u v (k+1)).1+
      Nat.dist (qmaBufferedDoglegPoint u v k).2 (qmaBufferedDoglegPoint u v (k+1)).2 = 1 := by
  unfold qmaBufferedDoglegPoint qmaBufferedDoglegLength at *
  split_ifs <;> simp_all [Nat.dist] <;> omega

theorem qmaBufferedDogleg_injective {u v : ℕ} (hu : 24 ≤ u) (hv : 23 ≤ v) (hne : u ≠ v) :
    Function.Injective (fun k : Fin (qmaBufferedDoglegLength u v+1) => qmaBufferedDoglegPoint u v k.val) := by
  intro k j h
  have hk := k.isLt
  have hj := j.isLt
  apply Fin.ext
  change qmaBufferedDoglegPoint u v k.val = qmaBufferedDoglegPoint u v j.val at h
  unfold qmaBufferedDoglegPoint qmaBufferedDoglegLength at *
  split_ifs at h <;> simp_all <;> omega

theorem qmaBufferedDogleg_length_bound {u v U : ℕ} (hu : u ≤ U) (hv : v ≤ u+1) :
    qmaBufferedDoglegLength u v ≤ 2*U+2 := by
  unfold qmaBufferedDoglegLength
  omega

theorem qmaBufferedFanout_direct_support (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (k : ℕ) :
    qmaBufferedFanoutSupport c side 0
      (qmaBufferedDoglegPoint (qmaBufferedPort c 0) (qmaBufferedOffset c side 0) k) := by
  have hb := qmaBufferedOffset_bounds c side 0
  have hu : 24 ≤ qmaBufferedPort c 0 := by unfold qmaBufferedPort; omega
  have hv : 23 ≤ qmaBufferedOffset c side 0 := by omega
  exact qmaBufferedDogleg_support hu hv k

end ContinuumCoulomb

end OAI
