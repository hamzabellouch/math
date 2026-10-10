import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InverseLinearRecovery
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.OrbitLoss
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.RecoverySupport
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.EquivOrbitTransport

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.JointOrbitRecovery

variable {K G X Y Z : Type*} [CommSemiring K] [Group G] [Fintype G]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

def SeparatedLoss {V : Type*} [DecidableEq V] [MulAction G V]
    (pass assigned : V → Prop) [DecidablePred pass] [DecidablePred assigned]
    (C : ℝ) (N : ℕ) (v : V) : Prop :=
  (((OrbitCounting.orbitSet (G := G) v).filter fun w => ¬pass w).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) v).card ≤ C / N ∧
  (((OrbitCounting.orbitSet (G := G) v).filter fun w => pass w ∧ ¬assigned w).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) v).card ≤ 1 / N

theorem separatedLoss_transport {U V : Type*} [DecidableEq U] [DecidableEq V]
    [MulAction G V] (e : U ≃ V)
    (pass assigned : U → Prop) [DecidablePred pass] [DecidablePred assigned]
    (C : ℝ) (N : ℕ) (u : U) :
    letI : MulAction G U := EquivOrbitTransport.action e
    SeparatedLoss (G := G) pass assigned C N u ↔
      SeparatedLoss (G := G) (pass ∘ e.symm) (assigned ∘ e.symm) C N (e u) := by
  let : MulAction G U := EquivOrbitTransport.action e
  unfold SeparatedLoss
  rw [EquivOrbitTransport.rejected_fraction e (fun w => ¬pass w) u,
    EquivOrbitTransport.rejected_fraction e (fun w => pass w ∧ ¬assigned w) u]
  simp only [Function.comp_def]

theorem combined_loss {V : Type*} [DecidableEq V] [MulAction G V]
    (pass assigned : V → Prop) [DecidablePred pass] [DecidablePred assigned]
    (C : ℝ) (N : ℕ) (v : V) (h : SeparatedLoss (G := G) pass assigned C N v) :
    (((OrbitCounting.orbitSet (G := G) v).filter fun w => ¬(assigned w ∧ pass w)).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) v).card ≤ (C + 1) / N := by
  simpa only [and_comm] using
    OrbitLoss.combined_inverse_linear (OrbitCounting.orbitSet (G := G) v)
      pass assigned C N h.1 h.2

theorem repair_of_separated_losses
    (Q H : Tensor K X Y Z)
    (passX assignedX : X → Prop) (passY assignedY : Y → Prop)
    (passZ assignedZ : Z → Prop)
    [DecidablePred passX] [DecidablePred assignedX]
    [DecidablePred passY] [DecidablePred assignedY]
    [DecidablePred passZ] [DecidablePred assignedZ]
    (hhole : H = ExactRecovery.delete Q
      (fun x => assignedX x ∧ passX x) (fun y => assignedY y ∧ passY y)
      (fun z => assignedZ z ∧ passZ z))
    (hpreserve : ∀ (g : G) x y z, Q (g • x) (g • y) (g • z) = Q x y z)
    {b C : ℝ} {N : ℕ} (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hN : 3 * (C + 1) < (N : ℝ))
    (hsupport : ((RecoverySupport.support Q).card : ℝ) ≤ Real.exp (b * N))
    (hx : ∀ x, (∃ y z, Q x y z ≠ 0) →
      SeparatedLoss (G := G) passX assignedX C N x)
    (hy : ∀ y, (∃ x z, Q x y z ≠ 0) →
      SeparatedLoss (G := G) passY assignedY C N y)
    (hz : ∀ z, (∃ x y, Q x y z ≠ 0) →
      SeparatedLoss (G := G) passZ assignedZ C N z) :
    InverseLinearRecovery.RecoveredBy Q H (RecoveryGrowth.shiftCount b (C + 1) N) := by
  classical
  rw [hhole]
  apply InverseLinearRecovery.repair_inverse_linear Q
    (fun x => assignedX x ∧ passX x) (fun y => assignedY y ∧ passY y)
    (fun z => assignedZ z ∧ passZ z) hpreserve hb (by linarith) hN
  · have heq : (@Finset.filter (X × Y × Z)
        (fun p => Q p.1 p.2.1 p.2.2 ≠ 0) (Classical.decPred _) Finset.univ) =
        RecoverySupport.support Q := by
      ext p
      simp only [RecoverySupport.support, Finset.mem_filter]
    rw [heq]
    exact hsupport
  · intro x hused
    exact combined_loss passX assignedX C N x (hx x hused)
  · intro y hused
    exact combined_loss passY assignedY C N y (hy y hused)
  · intro z hused
    exact combined_loss passZ assignedZ C N z (hz z hused)

theorem subexponential_copies {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C) :
    Filter.Tendsto (fun N : ℕ =>
      Real.log (Fintype.card
        (InverseLinearRecovery.MaskRectangles (RecoveryGrowth.shiftCount b (C + 1) N))) / N)
      Filter.atTop (nhds 0) :=
  InverseLinearRecovery.subexponential_copies hb (by linarith)

end MatrixMultiplication.JointOrbitRecovery

end OAI
