import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedPortRealization
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortLinks

namespace OAI

/-! The physical port graph has only the three local interaction geometries. -/

noncomputable section
namespace ContinuumCoulomb
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem portGraph_link (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    {x y : ℕ × ℕ} (h : (M.portGraph hd).Adj x y) : QMAPortLink x y := by
  change x ≠ y ∧ _ at h
  rcases h.2 with ⟨e,k,hk,rfl,rfl⟩ | ⟨e,k,hk,rfl,rfl⟩
  · exact qmaPortChain_link _ (M.coarseLength_pos hd e) (M.coarseRoute_step hd e) k hk
  · exact (qmaPortChain_link _ (M.coarseLength_pos hd e) (M.coarseRoute_step hd e) k hk).symm

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
