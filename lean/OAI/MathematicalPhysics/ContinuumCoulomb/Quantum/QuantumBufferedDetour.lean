import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedDogleg

namespace OAI

/-! Explicit western detour for the third buffered endpoint arm. -/

namespace ContinuumCoulomb

def qmaBufferedDetourPoint (u v k : ℕ) : ℕ × ℕ :=
  if k ≤ 8 then (17-k,17)
  else if k ≤ u then (9,k+9)
  else if k ≤ u+v-9 then (k-u+9,u+9)
  else if k ≤ u+v then (v,2*u+v-k)
  else (u,u)

def qmaBufferedDetourSupport (u v : ℕ) (p : ℕ × ℕ) : Prop :=
  (p.2 = 17 ∧ 9 ≤ p.1 ∧ p.1 ≤ 17) ∨
  (p.1 = 9 ∧ 17 ≤ p.2 ∧ p.2 ≤ u+9) ∨
  (p.2 = u+9 ∧ 9 ≤ p.1 ∧ p.1 ≤ v) ∨
  (p.1 = v ∧ u ≤ p.2 ∧ p.2 ≤ u+9) ∨
  (p.2 = u ∧ qmaBetween v u p.1)

theorem qmaBufferedDetour_zero (u v : ℕ) : qmaBufferedDetourPoint u v 0 = (17,17) := by
  simp [qmaBufferedDetourPoint]

theorem qmaBufferedDetour_last {u v : ℕ} (hu : 24 ≤ u) : qmaBufferedDetourPoint u v (u+v+1) = (u,u) := by
  unfold qmaBufferedDetourPoint
  by_cases h : u+v+1 ≤ 8
  · omega
  · rw [ite_eq_right h,ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega)]

theorem qmaBufferedDetour_support {u v : ℕ} (hu : 24 ≤ u) (hv : 23 ≤ v) (k : ℕ) :
    qmaBufferedDetourSupport u v (qmaBufferedDetourPoint u v k) := by
  unfold qmaBufferedDetourPoint
  split_ifs <;> simp [qmaBufferedDetourSupport,qmaBetween] <;> omega

theorem qmaBufferedDetour_step {u v : ℕ} (hu : 24 ≤ u) (hv : 23 ≤ v)
    (hclose : u ≤ v+1 ∧ v ≤ u+1) (hne : u ≠ v) (k : ℕ) (hk : k < u+v+1) :
    Nat.dist (qmaBufferedDetourPoint u v k).1 (qmaBufferedDetourPoint u v (k+1)).1+
      Nat.dist (qmaBufferedDetourPoint u v k).2 (qmaBufferedDetourPoint u v (k+1)).2 = 1 := by
  unfold qmaBufferedDetourPoint
  split_ifs <;> simp_all [Nat.dist] <;> omega

theorem qmaBufferedDetour_injective {u v : ℕ} (hu : 24 ≤ u) (hv : 23 ≤ v) (hne : u ≠ v) :
    Function.Injective (fun k : Fin (u+v+2) => qmaBufferedDetourPoint u v k.val) := by
  intro k j h
  have hk := k.isLt
  have hj := j.isLt
  apply Fin.ext
  change qmaBufferedDetourPoint u v k.val = qmaBufferedDetourPoint u v j.val at h
  unfold qmaBufferedDetourPoint at h
  split_ifs at h <;> simp_all <;> omega

theorem qmaBufferedFanout_detour_support (c : Fin 3 → ℕ) (side : Fin 3 → Bool) (k : ℕ) :
    qmaBufferedFanoutSupport c side 2
      (qmaBufferedDetourPoint (qmaBufferedPort c 2) (qmaBufferedOffset c side 2) k) := by
  have hb := qmaBufferedOffset_bounds c side 2
  have hu : 24 ≤ qmaBufferedPort c 2 := by unfold qmaBufferedPort; omega
  have hv : 23 ≤ qmaBufferedOffset c side 2 := by omega
  have hs := qmaBufferedDetour_support hu hv k
  have he : qmaBufferedPort c 2+9 = 8*(c 2+4)+1 := by unfold qmaBufferedPort; omega
  simpa [qmaBufferedDetourSupport,qmaBufferedFanoutSupport,he] using hs

end ContinuumCoulomb

end OAI
