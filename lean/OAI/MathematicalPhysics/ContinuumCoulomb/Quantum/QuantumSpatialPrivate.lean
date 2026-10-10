import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialXZBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPrivateSupported

namespace OAI

/-! Private-pair subdivision preserves bounded spatial density. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem QMASpatialXZModel.private {A B : ℕ} (M : QMASpatialXZModel A B)
    {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : QMASpatialXZModel (A+B) (4*B),
      (∀ p q, (qmaPauliSupport (G.word p)).card = 2 →
        qmaPauliSupport (G.word p) = qmaPauliSupport (G.word q) → p = q) ∧
      |G.toQMAXZModel.energy-M.toQMAXZModel.energy| ≤ 1/N ∧
      G.rows = M.rows ∧ G.width = M.width := by
  obtain ⟨v,K,hvy,hv,hprivate,hvs,he⟩ :=
    qmaXZPrivate_supported M.word M.coefficient M.card M.noY hN
  let cell := qmaMediatorCell M.cell M.anchor
  let anchor := fun p : M.Term × Fin 4 => M.anchor p.1
  let G : QMASpatialXZModel (A+B) (4*B) := {
    toQMAXZModel := QMAXZModel.ofWords v K hvy hv
    rows := M.rows
    width := M.width
    cell := cell
    anchor := anchor
    geometry := by
      intro e q hq
      exact qmaMediatorSupport_geometry M.cell M.anchor (qmaPauliSupport (M.word e.1)) e.1
        (M.geometry e.1) q (hvs e hq)
    qubitDensity := by
      intro p
      change (Finset.univ.filter (fun q : M.Q ⊕ M.Term => cell q = p)).card ≤ _
      rw [qmaSumFilter_card]
      exact Nat.add_le_add (M.qubitDensity p) (M.termDensity p)
    termDensity := by
      intro p
      change (Finset.univ.filter (fun e : M.Term × Fin 4 => M.anchor e.1 = p)).card ≤ _
      rw [qmaProdFilter_card (α := M.Term) 4 (fun e => M.anchor e = p)]
      exact Nat.mul_le_mul_left 4 (M.termDensity p) }
  refine ⟨G,hprivate,?_,rfl,rfl⟩
  change |(QMAXZModel.ofWords v K hvy hv).energy-M.toQMAXZModel.energy| ≤ 1/N
  rw [QMAXZModel.ofWords_energy]
  exact he

end ContinuumCoulomb

end

end OAI
