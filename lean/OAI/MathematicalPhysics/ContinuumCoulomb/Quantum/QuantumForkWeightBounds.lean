import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkStateMatrix

namespace OAI

/-! Coefficient growth of the repeatable fork stage is polynomial. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaForkOffset_abs_le {J K L : ℝ} (hL : 1 ≤ L) (hJ : |J| ≤ L) (hK : |K| ≤ L) :
    |qmaForkOffset J K| ≤ 7*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hJ2 : J^2 ≤ L^2 := by nlinarith [sq_abs J,mul_self_le_mul_self (abs_nonneg J) hJ]
  have hK2 : K^2 ≤ L^2 := by nlinarith [sq_abs K,mul_self_le_mul_self (abs_nonneg K) hK]
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
  rw [abs_of_nonneg (by unfold qmaForkOffset; positivity)]
  unfold qmaForkOffset
  nlinarith

namespace QMAForkState
variable {n c : ℕ} {d : Fin c → ℕ} {ν : Type*} [Fintype ν]
variable (G : QMAForkState n c d ν)

theorem nextWeight_abs_le (R : ℝ) (w : ν → ℝ) (J : (Σ i, Fin (d i)) → ℝ)
    {L : ℝ} (hL : 1 ≤ L) (hR : |R| ≤ L) (hw : ∀ e, |w e| ≤ L)
    (hJ : ∀ p, |J p| ≤ L) (e : G.NextEdge) : |G.nextWeight R w J e| ≤ 2*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hL2 : L ≤ L^2 := by nlinarith
  rcases e with (e | e) | (e | ⟨e,b⟩)
  · exact (hw e).trans (by nlinarith)
  · change |2*G.pairWeight J 0 e*G.pairWeight J 1 e| ≤ _
    rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hp := mul_le_mul (hJ (qmaForkPairedPort d (G.ports.pairEquiv.symm e,0)))
      (hJ (qmaForkPairedPort d (G.ports.pairEquiv.symm e,1)))
      (abs_nonneg _) hL0
    dsimp [pairWeight] at *
    nlinarith
  · change |R^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg R)]
    nlinarith [mul_self_le_mul_self (abs_nonneg R) hR,sq_abs R]
  · change |2*R*G.pairWeight J b e| ≤ _
    rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hp := mul_le_mul hR (hJ (qmaForkPairedPort d (G.ports.pairEquiv.symm e,b)))
      (abs_nonneg _) hL0
    dsimp [pairWeight] at *
    nlinarith

theorem nextActive_abs_le (R : ℝ) (J : (Σ i, Fin (d i)) → ℝ) {L : ℝ}
    (hR : |R| ≤ L) (hJ : ∀ p, |J p| ≤ L) (p : Σ i, Fin (d i / 2 + d i % 2)) :
    |G.nextActive R J p| ≤ L := by
  unfold nextActive
  split
  · exact hR
  · exact hJ _

theorem nextConstant_abs_le (R constant : ℝ) (J : (Σ i, Fin (d i)) → ℝ)
    {L : ℝ} (hL : 1 ≤ L) (hR : |R| ≤ L) (hJ : ∀ p, |J p| ≤ L) :
    |G.nextConstant R constant J| ≤ |constant|+10*(G.ports.pairCount:ℝ)*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hR2 : R^2 ≤ L^2 := by nlinarith [mul_self_le_mul_self (abs_nonneg R) hR,sq_abs R]
  have hs : |∑ e, qmaForkOffset (G.pairWeight J 0 e) (G.pairWeight J 1 e)| ≤
      (G.ports.pairCount:ℝ)*(7*L^2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _e : Fin G.ports.pairCount, 7*L^2 := Finset.sum_le_sum (fun e _ =>
        qmaForkOffset_abs_le hL (hJ _) (hJ _))
      _ = _ := by simp
  unfold nextConstant
  have hb := abs_add_le (constant+∑ e, qmaForkOffset (G.pairWeight J 0 e) (G.pairWeight J 1 e))
    (3*(G.ports.pairCount:ℝ)*R^2)
  have hc := abs_add_le constant (∑ e, qmaForkOffset (G.pairWeight J 0 e) (G.pairWeight J 1 e))
  rw [abs_of_nonneg (by positivity : 0 ≤ 3*(G.ports.pairCount:ℝ)*R^2)] at hb
  nlinarith [mul_le_mul_of_nonneg_left hR2 (by positivity : 0 ≤ (G.ports.pairCount:ℝ))]

end QMAForkState
end ContinuumCoulomb

end

end OAI
