import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedSupport

namespace OAI

/-! Buffered routes lie strictly inside the nonnegative lattice quadrant. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem endpointArmSupport_positive (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) {z : ℕ × ℕ} (hz : M.endpointArmSupport hd v e z) :
    0 < z.1 ∧ 0 < z.2 := by
  obtain ⟨p,hp,hs⟩ := hz
  have hb := qmaBufferedFanout_bounded (M.endpointColors hd v)
    ((M.endpointPorts hd v).increasing (show (0 : Fin 3) < 1 by decide))
    ((M.endpointPorts hd v).increasing (show (1 : Fin 3) < 2 by decide))
    ((M.endpointPorts hd v).slot 2).isLt (fun _ => false) _ hs
  rw [← hp]
  dsimp [qmaBufferedCellPoint]
  omega

theorem spacedSupport_positive (e : M.Term) {z : ℕ × ℕ} (hz : M.spacedSupport e z) :
    0 < z.1 ∧ 0 < z.2 := by
  have hc : 0 < (M.spacedColor e).val := by
    dsimp [spacedColor,qmaSpacedLaneColor]
    omega
  rcases hz with ⟨hy,hx⟩ | ⟨hx,hy⟩ <;>
    dsimp [qmaLanePoint,qmaBetween] at * <;> omega

theorem bufferedPath_positive (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) {z : ℕ × ℕ} (hz : z ∈ (M.bufferedPath hd e).val.support) :
    0 < z.1 ∧ 0 < z.2 := by
  rcases M.bufferedPath_support hd e hz with h | h | h
  · exact M.endpointArmSupport_positive hd _ _ h
  · exact M.spacedSupport_positive e h
  · exact M.endpointArmSupport_positive hd _ _ h

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
