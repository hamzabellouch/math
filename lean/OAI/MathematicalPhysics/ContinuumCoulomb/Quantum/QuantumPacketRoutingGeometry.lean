import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarTapeGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPacketGeometry

namespace OAI

/-! Packet support and the finite permission table suffice to recover the
actual emitted planar family and its final nearest-neighbor embedding. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPlanarTapeGeometry
open QuantumPlanarTapeProgram
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) (x : Input)
    (hg : QMAPacketGeometry (P.crossingOutput N hD) (P.crossingPosition N D) x.1.1 x.1.2)
    (hallowed : ∀ B, QuantumRoutingTable.allowed x.2 B =
      QuantumRoutingTable.allowed P.routingTable B)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)
    {X Y : ℕ}
    (hsource : ∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y)
    (hpath : ∀ e k, k ≤ P.length e → (P.point e k).1 < X ∧ (P.point e k).2 < Y)

include hD hg hallowed havoid hpositive hsource hpath in
theorem planar_family :
    ∃ R : QMAPlanarRouteData (graph x hg.noLoops),
      (N,value x) = QuantumEvenTapeGeometry.input R (Equiv.refl _) N ∧
      (∀ e, R.length e ≤ 20) ∧ R.Bounded (32*X) (32*Y) := by
  obtain ⟨v,hpos,hforward,hbackward⟩ := hg.matching
  exact ⟨route P N hD x hg.bounded hg.noLoops v hforward hbackward havoid hpositive,
    even_input_eq P N hD x hg.bounded hg.noLoops v hforward hbackward havoid hpositive
      hpos hallowed N,
    route_length P N hD x hg.bounded hg.noLoops v hforward hbackward havoid hpositive,
    route_bounded P N hD x hg.bounded hg.noLoops v hforward hbackward havoid hpositive
      hsource hpath⟩

include hD hg hallowed havoid hpositive hsource hpath in
theorem final_realization (hN : 0 < N) :
    let s := QuantumListRouteProgram.iterate N QuantumFinalRoutingProgram.rounds
      (QuantumEvenTapeProgram.value (N,value x))
    ∃ (hs : QuantumListSchedule.Valid s.1)
      (Q : QMAPathEmbedding (QuantumListSchedule.schedule s.1 hs)),
      QuantumListRouteProgram.Represents s hs Q ∧ Q.Bounded (256*X) (256*Y) ∧
      (∀ e, qmaSquareGrid.Adj (Q.position ((QuantumListSchedule.schedule s.1 hs).graph.left e))
        (Q.position ((QuantumListSchedule.schedule s.1 hs).graph.right e))) := by
  obtain ⟨R,hinput,hL,hbox⟩ := planar_family P N hD x hg hallowed havoid hpositive hsource hpath
  have h := QuantumEvenTapeGeometry.realizes R (Equiv.refl _) N hN hL hbox
  rw [← hinput] at h
  obtain ⟨hs,Q,hQ,hbox',hgrid,_,_⟩ := h
  exact ⟨hs,Q,hQ,by simpa only [← Nat.mul_assoc,show 8*32=256 by decide] using hbox',hgrid⟩

end ContinuumCoulomb.QuantumPlanarTapeGeometry

end

end OAI
