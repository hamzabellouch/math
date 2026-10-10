import OAI.Combinatorics.Crossing.FourCycles
import OAI.Combinatorics.Crossing.RectangleAlgebra

namespace OAI

noncomputable section
namespace Zarankiewicz

def edgeBlock {m n : ℕ} (J : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ)
    (i k : Fin m) : Matrix (Fin n) (Fin n) ℝ := fun p q => J (i,p) (k,q)

def blockRectangle {m n : ℕ} (J : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ)
    (i k i₀ : Fin m) : Matrix (Fin n) (Fin n) ℝ :=
  edgeBlock J i k - edgeBlock J i i₀ - edgeBlock J i₀ k + edgeBlock J i₀ i₀

theorem fourCycle_pairing_rectangle {m n : ℕ}
    (J : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ)
    (i k i₀ : Fin m) (p p' q q' : Fin n) :
    edgePairing J (walkEdgeChain (fourCycleWalk i i₀ p p'))
      (walkEdgeChain (fourCycleWalk k i₀ q q')) =
      blockRectangle J i k i₀ p q - blockRectangle J i k i₀ p q' -
        blockRectangle J i k i₀ p' q + blockRectangle J i k i₀ p' q' := by
  rw [fourCycleWalk_chain, fourCycleWalk_chain]
  simp only [edgePairing_add_left, edgePairing_sub_left, edgePairing_add_right,
    edgePairing_sub_right, edgePairing_single]
  simp only [blockRectangle, edgeBlock, Matrix.add_apply, Matrix.sub_apply]
  ring

end Zarankiewicz

end

end OAI
