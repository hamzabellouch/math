import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedFanout
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteLanes

namespace OAI

/-! Buffered endpoint cells align with spaced lanes and are mutually disjoint. -/

namespace ContinuumCoulomb

def qmaBufferedCellPoint (C : ℕ) (p z : ℕ × ℕ) : ℕ × ℕ :=
  (8*(C+6)*p.1+z.1,8*(C+6)*p.2+z.2)

def qmaBufferedLaneColor {C : ℕ} (c : Fin C) : Fin (C+6) := ⟨c.val+3,by omega⟩

theorem qmaBufferedLaneColor_injective (C : ℕ) : Function.Injective (@qmaBufferedLaneColor C) := by
  intro a b h
  apply Fin.ext
  have hh := congrArg Fin.val h
  dsimp [qmaBufferedLaneColor] at hh
  omega

theorem qmaBufferedFanout_bounded (c : Fin 3 → ℕ) (h01 : c 0 < c 1) (h12 : c 1 < c 2)
    {C : ℕ} (hC : c 2 < C) (side : Fin 3 → Bool) (a : Fin 3) {z : ℕ × ℕ}
    (hz : qmaBufferedFanoutSupport c side a z) :
    0 < z.1 ∧ z.1 < 8*(C+6) ∧ 0 < z.2 ∧ z.2 < 8*(C+6) := by
  have h0 := qmaBufferedOffset_bounds c side 0
  have h1 := qmaBufferedOffset_bounds c side 1
  have h2 := qmaBufferedOffset_bounds c side 2
  dsimp [qmaBufferedPort] at h0 h1 h2
  fin_cases a <;> simp [qmaBufferedFanoutSupport,qmaBufferedPort,qmaBetween] at hz <;> omega

theorem qmaBufferedCellPoint_cell (C : ℕ) (p z : ℕ × ℕ)
    (hx : z.1 < 8*(C+6)) (hy : z.2 < 8*(C+6)) :
    ((qmaBufferedCellPoint C p z).1/(8*(C+6)),
      (qmaBufferedCellPoint C p z).2/(8*(C+6))) = p := by
  have hw : 0 < 8*(C+6) := by omega
  apply Prod.ext <;> dsimp [qmaBufferedCellPoint]
  · rw [Nat.add_comm,Nat.add_mul_div_left _ _ hw,Nat.div_eq_of_lt hx,zero_add]
  · rw [Nat.add_comm,Nat.add_mul_div_left _ _ hw,Nat.div_eq_of_lt hy,zero_add]

theorem qmaBufferedCellPoint_disjoint {C : ℕ} {p q x y : ℕ × ℕ} (hpq : p ≠ q)
    (hx : x.1 < 8*(C+6) ∧ x.2 < 8*(C+6))
    (hy : y.1 < 8*(C+6) ∧ y.2 < 8*(C+6)) :
    qmaBufferedCellPoint C p x ≠ qmaBufferedCellPoint C q y := by
  intro h
  have hd := congrArg (fun z : ℕ × ℕ => (z.1/(8*(C+6)),z.2/(8*(C+6)))) h
  rw [qmaBufferedCellPoint_cell C p x hx.1 hx.2,qmaBufferedCellPoint_cell C q y hy.1 hy.2] at hd
  exact hpq hd

theorem qmaBufferedEndpoint_alignment {C : ℕ} (p : ℕ × ℕ) (c : Fin 3 → ℕ)
    (a : Fin 3) (hc : c a < C) :
    qmaBufferedCellPoint C p (qmaBufferedPort c a,qmaBufferedPort c a) =
      (8*(qmaLanePoint (qmaBufferedLaneColor ⟨c a,hc⟩) p).1,
       8*(qmaLanePoint (qmaBufferedLaneColor ⟨c a,hc⟩) p).2) := by
  apply Prod.ext <;> dsimp [qmaBufferedCellPoint,qmaBufferedPort,qmaLanePoint,qmaBufferedLaneColor] <;> ring

end ContinuumCoulomb

end OAI
