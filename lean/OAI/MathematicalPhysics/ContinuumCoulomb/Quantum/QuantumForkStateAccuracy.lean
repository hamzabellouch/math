import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkStateNextMatrix

namespace OAI

/-! Full-space spectral error of the repeatable active-star transition. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical
namespace QMAForkState
variable {n c : ℕ} {d : Fin c → ℕ} {ν : Type*} [Fintype ν]
variable (G : QMAForkState n c d ν)

theorem next_accuracy (w : ν → ℝ) (J : (Σ i, Fin (d i)) → ℝ)
    (constant : ℝ) {N : ℝ} (hN : 0 < N) :
    let B := 3*(∑ a, |G.retainedWeight w J a|)+|constant|
    let A := 3*∑ e, (1+2*|G.pairWeight J 0 e|+2*|G.pairWeight J 1 e|)
    let D := B+12*∑ e, (1+|G.pairWeight J 0 e|+|G.pairWeight J 1 e|)^2
    let R := qmaRoutingScale A D N
    |sourceMatrixBottom (n+G.ports.pairCount*2)
        (G.next.matrix (G.nextWeight R w J) (G.nextActive R J) (G.nextConstant R constant J)) -
      sourceMatrixBottom n (G.matrix w J constant)| ≤ 1/N := by
  dsimp only
  rw [G.next_matrix_is_forks,G.matrix_pair_split]
  exact qmaForksGraph_accuracy G.retainedLeft G.retainedRight G.retained_distinct
    (G.retainedWeight w J) constant G.ports.site G.ports.site_injective
    (G.pairWeight J 0) (G.pairWeight J 1) hN

end QMAForkState
end ContinuumCoulomb

end

end OAI
