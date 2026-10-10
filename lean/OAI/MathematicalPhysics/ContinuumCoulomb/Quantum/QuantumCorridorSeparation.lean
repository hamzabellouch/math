import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCorridorEndpoints
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumInternalHalfSeparation
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCorridorInterior

namespace OAI

/-! Complete corridor separation: internal paths only meet corridors at their
terminals, and different physical corridors have disjoint full paths. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem internal_corridor_disjoint (p q : ℕ × ℕ) (e : QMAInternalEdge) (a : Fin 4)
    (b c : Bool) (he : P.RoutingAllowed (qmaInternalBody p e))
    (hc : P.RoutingAllowed (.corridor q a b c)) :
    Disjoint ((((qmaInternalBody p e).path).drop 1).dropLast).toFinset
      (qmaCellCorridor q a b c).toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  obtain ⟨t,ht⟩ := qmaCellCorridor_mem_half (List.mem_toFinset.mp hw)
  exact Finset.disjoint_left.mp (P.internal_halfAt_disjoint p (qmaCorridorHalfCell q a t) e
    (qmaCorridorHalfPort a t) (qmaCorridorHalfMode b c t) he
    (qmaCorridorHalf_mode P.IsCrossing q a b c hc.1 hc.2 t)) hz (List.mem_toFinset.mpr ht)

theorem corridor_internal_disjoint (p q : ℕ × ℕ) (a : Fin 4) (b c : Bool) (e : QMAInternalEdge)
    (hp : 0 < p.1 ∧ 0 < p.2) (hc : P.RoutingAllowed (.corridor p a b c))
    (he : P.RoutingAllowed (qmaInternalBody q e)) :
    Disjoint (((qmaCellCorridor p a b c).drop 1).dropLast).toFinset
      (qmaInternalBody q e).path.toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  rcases qmaCellCorridor_interior hp (List.mem_toFinset.mp hz) with h | h
  · exact Finset.disjoint_left.mp (P.halfAt_internal_disjoint p q a b e he hc.1)
      (List.mem_toFinset.mpr h) hw
  · exact Finset.disjoint_left.mp (P.halfAt_internal_disjoint (qmaGridNeighbor p a) q
      (qmaPortOpposite a) c e he hc.2) (List.mem_toFinset.mpr h) hw

theorem corridors_disjoint (p q : ℕ × ℕ) (a d : Fin 4) (b c f g : Bool)
    (hp : 0 < p.1 ∧ 0 < p.2) (hq : 0 < q.1 ∧ 0 < q.2)
    (hR : P.RoutingAllowed (.corridor p a b c)) (hS : P.RoutingAllowed (.corridor q d f g))
    (hne : s((QMACellRouteBody.corridor p a b c).source,(QMACellRouteBody.corridor p a b c).target) ≠
      s((QMACellRouteBody.corridor q d f g).source,(QMACellRouteBody.corridor q d f g).target)) :
    Disjoint (qmaCellCorridor p a b c).toFinset (qmaCellCorridor q d f g).toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  obtain ⟨t,ht⟩ := qmaCellCorridor_mem_half (List.mem_toFinset.mp hz)
  obtain ⟨u,hu⟩ := qmaCellCorridor_mem_half (List.mem_toFinset.mp hw)
  have hc := qmaHalfPathAt_collision P.IsCrossing
    (qmaCorridorHalf_mode P.IsCrossing p a b c hR.1 hR.2 t)
    (qmaCorridorHalf_mode P.IsCrossing q d f g hS.1 hS.2 u) ht hu
  apply hne
  rw [qmaCorridorBody_half_pair P.IsCrossing p hp a b c hR.1 hR.2 t,
    qmaCorridorBody_half_pair P.IsCrossing q hq d f g hS.1 hS.2 u,hc.1,hc.2]

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
