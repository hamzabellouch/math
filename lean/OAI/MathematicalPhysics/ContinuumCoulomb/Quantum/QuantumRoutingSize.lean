import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingsGraph
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathsGraph

namespace OAI

/-! Linear graph-size growth and an explicit polynomial routing penalty bound. -/

noncomputable section
namespace ContinuumCoulomb

abbrev QMAForkGraphEdge (ν : Type*) (r : ℕ) :=
  (ν ⊕ Fin r) ⊕ (Fin r ⊕ (Fin r × Fin 3))
abbrev QMACrossingsGraphEdge (ν : Type*) (r : ℕ) :=
  (ν ⊕ (Fin r × Fin 4)) ⊕ (Fin r ⊕ (Fin r × Fin 4))
abbrev QMAPathsGraphEdge (ν : Type*) (r : ℕ) :=
  ν ⊕ (Fin r ⊕ (Fin r × Fin 2))

theorem qmaForkGraphEdge_card (ν : Type*) [Fintype ν] (r : ℕ) :
    Fintype.card (QMAForkGraphEdge ν r) = Fintype.card ν+5*r := by
  simp only [QMAForkGraphEdge,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

theorem qmaCrossingsGraphEdge_card (ν : Type*) [Fintype ν] (r : ℕ) :
    Fintype.card (QMACrossingsGraphEdge ν r) = Fintype.card ν+9*r := by
  simp only [QMACrossingsGraphEdge,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

theorem qmaPathsGraphEdge_card (ν : Type*) [Fintype ν] (r : ℕ) :
    Fintype.card (QMAPathsGraphEdge ν r) = Fintype.card ν+3*r := by
  simp only [QMAPathsGraphEdge,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

theorem qmaRoutingScale_polynomial {A B N : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 0 ≤ N) :
    qmaRoutingScale A B N ≤ 21*(A+B+1)^3*(N+1) := by
  let Q := A+B+1
  have hQ : 1 ≤ Q := by dsimp [Q]; linarith
  have hQ0 : 0 ≤ Q := le_trans (by norm_num) hQ
  have hQ2 : 1 ≤ Q^2 := one_le_pow₀ hQ
  have hQ3 : Q ≤ Q^3 := by nlinarith [mul_le_mul_of_nonneg_left hQ2 hQ0]
  have hQ31 : 1 ≤ Q^3 := hQ.trans hQ3
  have hn : 0 ≤ Q^3*N := mul_nonneg (by positivity) hN
  change 16*Q^3*N+4*Q+1 ≤ 21*Q^3*(N+1)
  nlinarith

end ContinuumCoulomb

end

end OAI
