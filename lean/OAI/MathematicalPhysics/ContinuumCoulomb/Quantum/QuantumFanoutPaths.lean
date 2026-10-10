import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFanoutPorts

namespace OAI

/-! Explicit simple unit-step paths for the three endpoint arms. -/

namespace ContinuumCoulomb

def qmaFanoutLength (c : Fin 3 → ℕ) : Fin 3 → ℕ := ![2*c 0+2,2*c 1+2,2*c 2+6]

def qmaFanoutPoint (c : Fin 3 → ℕ) (a : Fin 3) (k : ℕ) : ℕ × ℕ :=
  if a = 0 then
    if k ≤ c 0+1 then (2+k,2) else (c 0+3,2+(k-(c 0+1)))
  else if a = 1 then
    if k ≤ c 1+1 then (2,2+k) else (2+(k-(c 1+1)),c 1+3)
  else if k = 0 then (2,2)
  else if k ≤ c 2+3 then (1,k+1)
  else if k ≤ 2*c 2+5 then (k-(c 2+3)+1,c 2+4)
  else (c 2+3,c 2+3)

theorem qmaFanoutPoint_zero (c : Fin 3 → ℕ) (a : Fin 3) : qmaFanoutPoint c a 0 = (2,2) := by
  fin_cases a <;> simp [qmaFanoutPoint]

theorem qmaFanoutPoint_last (c : Fin 3 → ℕ) (a : Fin 3) :
    qmaFanoutPoint c a (qmaFanoutLength c a) = qmaFanoutPort c a := by
  fin_cases a
  · change (if 2*c 0+2 ≤ c 0+1 then (2+(2*c 0+2),2)
      else (c 0+3,2+((2*c 0+2)-(c 0+1)))) = (c 0+3,c 0+3)
    rw [ite_eq_right (by omega)]
    apply Prod.ext
    · rfl
    · dsimp; omega
  · change (if 2*c 1+2 ≤ c 1+1 then (2,2+(2*c 1+2))
      else (2+((2*c 1+2)-(c 1+1)),c 1+3)) = (c 1+3,c 1+3)
    rw [ite_eq_right (by omega)]
    apply Prod.ext
    · dsimp; omega
    · rfl
  · change (if 2*c 2+6 = 0 then (2,2) else if 2*c 2+6 ≤ c 2+3 then (1,2*c 2+6+1)
      else if 2*c 2+6 ≤ 2*c 2+5 then (2*c 2+6-(c 2+3)+1,c 2+4)
      else (c 2+3,c 2+3)) = (c 2+3,c 2+3)
    rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega)]

theorem qmaFanoutPoint_support (c : Fin 3 → ℕ) (a : Fin 3) (k : ℕ)
    (hk : k ≤ qmaFanoutLength c a) : qmaFanoutSupport c a (qmaFanoutPoint c a k) := by
  fin_cases a <;> simp only [qmaFanoutPoint,qmaFanoutLength,qmaFanoutSupport] at *
  all_goals split_ifs <;> simp_all <;> omega

theorem qmaFanoutPoint_step (c : Fin 3 → ℕ) (a : Fin 3) (k : ℕ)
    (hk : k < qmaFanoutLength c a) :
    Nat.dist (qmaFanoutPoint c a k).1 (qmaFanoutPoint c a (k+1)).1+
      Nat.dist (qmaFanoutPoint c a k).2 (qmaFanoutPoint c a (k+1)).2 = 1 := by
  fin_cases a <;> simp only [qmaFanoutPoint,qmaFanoutLength] at *
  all_goals split_ifs <;> simp_all [Nat.dist] <;> omega

theorem qmaFanoutPoint_injective (c : Fin 3 → ℕ) (a : Fin 3) :
    Function.Injective (fun k : Fin (qmaFanoutLength c a+1) => qmaFanoutPoint c a k.val) := by
  intro k j h
  have hk := k.isLt
  have hj := j.isLt
  apply Fin.ext
  fin_cases a <;> simp only [qmaFanoutPoint,qmaFanoutLength] at *
  all_goals split_ifs at h <;> simp_all <;> omega

theorem qmaFanout_length_bound (c : Fin 3 → ℕ) (h01 : c 0 < c 1) (h12 : c 1 < c 2)
    {C : ℕ} (hC : c 2 ≤ C) (a : Fin 3) : qmaFanoutLength c a ≤ 2*C+6 := by
  fin_cases a <;> simp [qmaFanoutLength] <;> omega

theorem qmaFanout_paths_meet (c : Fin 3 → ℕ) (h01 : c 0 < c 1) (h12 : c 1 < c 2)
    {a b : Fin 3} (hab : a ≠ b)
    (k : Fin (qmaFanoutLength c a+1)) (j : Fin (qmaFanoutLength c b+1))
    (h : qmaFanoutPoint c a k.val = qmaFanoutPoint c b j.val) : k.val = 0 ∧ j.val = 0 := by
  have hm := qmaFanout_only_center c h01 h12 hab
    (qmaFanoutPoint_support c a k.val (by omega))
    (h.symm ▸ qmaFanoutPoint_support c b j.val (by omega))
  have hk : k = ⟨0,by omega⟩ := qmaFanoutPoint_injective c a (by simpa [qmaFanoutPoint_zero] using hm)
  have hj : j = ⟨0,by omega⟩ := qmaFanoutPoint_injective c b (by simpa [qmaFanoutPoint_zero] using h.symm.trans hm)
  simp [hk,hj]

end ContinuumCoulomb

end OAI
